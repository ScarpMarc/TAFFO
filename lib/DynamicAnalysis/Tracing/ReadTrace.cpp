#include "ReadTrace.h"

#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/CommandLine.h"

#include <iostream>
#include <fstream>
#include <string>
#include <unordered_map>
#include <memory>

#include "TaffoUtils/Metadata.h"
#include "TaffoUtils/InputInfo.h"

using namespace llvm;

#define DEBUG_TYPE "read-trace"

cl::list<std::string> Filenames("trace_file", cl::desc("Specify filenames of trace files"), cl::ZeroOrMore);

//-----------------------------------------------------------------------------
// ReadTrace implementation
//-----------------------------------------------------------------------------
bool ReadTrace::runOnModule(Module &M) {
  bool Changed = false;

  auto &CTX = M.getContext();
  IRBuilder<> Builder(CTX);

  std::unordered_map<std::string, double> minVals, maxVals;
  std::unordered_map<std::string, mdutils::FloatType::FloatStandard> valTypes;
  std::unordered_map<Instruction*, double> derivedMinVals, derivedMaxVals;

  // calculate connected components on the memory operations
  std::unordered_map<Value*, int> instToIndex;
  std::unordered_map<int, Value*> indexToInst;
  std::list<std::pair<int, int>> edges;
  int instCount = buildMemEdgesList(M, instToIndex, indexToInst, edges);
  std::unordered_map<int, std::list<int>> cc;
  std::unordered_map<int, std::list<Value*>> ccValues;
  std::unordered_map<int, std::pair<double, double>> ccRanges;
  connectedComponents(instCount, edges, cc);

  for (auto &it : cc) {
    std::list<int> l = it.second;
    for (auto x : l) {
      ccValues[it.first].emplace_back(indexToInst[x]);
//      errs() << typeName(*indexToInst[x]) << ": ";
//      errs() << *indexToInst[x] << "\n";
    }
//    errs() << "-----\n";
  }

  // read the trace file
  parseTraceFiles(minVals, maxVals, valTypes);

  // calculate value ranges for every component
  calculateCCRanges(ccValues, minVals, maxVals, ccRanges);

  for (const auto &it : ccRanges) {
    const auto range = it.second;
    const auto l = ccValues[it.first];
    for (auto x : l) {
      errs() << typeName(*x) << ": ";
      errs() << "[" << range.first << ", " << range.second << "]: ";
      errs() << *x << "\n";
    }
    errs() << "-----\n";
  }

  // assign calculated intervals to the metadata
  std::unordered_map<Value*, std::pair<double, double>> valuesRanges;

  for (auto &F : M) {
    if (!F.hasName() || F.isDeclaration()) continue;
    for (auto &BB : F.getBasicBlockList()) {
      for (auto &Inst : BB.getInstList()) {
        if (Inst.isDebugOrPseudoInst()) continue;
        auto InstName = Inst.getName().str();
        if (minVals.count(InstName) > 0) {
          valuesRanges[&Inst] = {minVals.at(InstName), maxVals.at(InstName)};
        }
      } // instructions
    } // basic blocks
  } // functions

  for (const auto &it : ccRanges) {
    const auto range = it.second;
    const auto l = ccValues[it.first];
    for (auto value : l) {
      valuesRanges[value] = range;
    }
  }

  for (const auto &it: valuesRanges) {
    auto value = it.first;
    auto range = it.second;
    if (auto Inst = dyn_cast<Instruction>(value)) {
      if (isa<LoadInst>(Inst) && !Inst->getType()->isFPOrFPVectorTy()) continue;
      auto instType = std::shared_ptr<mdutils::FloatType>{};
      auto instRange = std::make_shared<mdutils::Range>(range.first, range.second);
      auto instError = std::shared_ptr<double>{};
      mdutils::InputInfo ii{instType, instRange, instError, false, true};
      mdutils::MetadataManager::setInputInfoMetadata(*Inst, ii);
      Changed = true;
    }
    if (auto Arg = dyn_cast<Argument>(value)) {
      auto F = Arg->getParent();
      auto instType = std::shared_ptr<mdutils::FloatType>{};
      auto instRange = std::make_shared<mdutils::Range>(range.first, range.second);
      auto instError = std::shared_ptr<double>{};
      mdutils::InputInfo ii{instType, instRange, instError, false, true};
      llvm::SmallVector<mdutils::MDInfo *> FunMD;
      mdutils::MetadataManager::getMetadataManager().retrieveArgumentInputInfo(*F, FunMD);
      if (!Arg->getType()->isStructTy()) {
        auto ArgMD = FunMD[Arg->getArgNo()];
        if (!ArgMD) {
          FunMD[Arg->getArgNo()] = new mdutils::InputInfo(ii);
        } else {
          auto *ArgII = dyn_cast<mdutils::InputInfo>(ArgMD);
          *ArgII = ii;
        }
        mdutils::MetadataManager::setArgumentInputInfoMetadata(*F, FunMD);
      }
    }
  }

  return Changed;
}

void ReadTrace::calculateCCRanges(const std::unordered_map<int, std::list<Value*>>& ccValues,
                                  const std::unordered_map<std::string, double>& minVals,
                                  const std::unordered_map<std::string, double>& maxVals,
                                  std::unordered_map<int, std::pair<double, double>>& ccRanges) {
  for (const auto& it: ccValues) {
    double minV, maxV;
    bool hasValue = false;
    for (const auto value: it.second) {
      auto valueName = value->getName().str();
      if (minVals.count(valueName) > 0) {
        if (!hasValue) {
          hasValue = true;
          minV = minVals.at(valueName);
          maxV = maxVals.at(valueName);
        } else {
          minV = minV <= minVals.at(valueName)? minV: minVals.at(valueName);
          maxV = maxV >= maxVals.at(valueName)? maxV: maxVals.at(valueName);
        }
      }
    }
    if (hasValue) {
      ccRanges[it.first] = {minV, maxV};
    }
  }
}

std::string ReadTrace::typeName(Value& val) {
  if (isa<Argument>(val)) {
    return "Argument";
  } else if (isa<Constant>(val)) {
    return "Constant";
  } else if (isa<Instruction>(val)) {
    return "Instruction";
  } else if (isa<Operator>(val)) {
    return "Operator";
  } else {
    return "Unknown";
  }
}

int merge(int* parent, int x)
{
  if (parent[x] == x)
    return x;
  return merge(parent, parent[x]);
}

void ReadTrace::connectedComponents(const int n, const std::list<std::pair<int, int>>& edges,
                                    std::unordered_map<int, std::list<int>>& cc) {
  int parent[n];
  for (int i = 0; i < n; i++) {
    parent[i] = i;
  }
  for (auto x : edges) {
    parent[merge(parent, x.first)] = merge(parent, x.second);
  }
  for (int i = 0; i < n; i++) {
    parent[i] = merge(parent, parent[i]);
  }
  for (int i = 0; i < n; i++) {
    cc[parent[i]].push_back(i);
  }
}

int ReadTrace::buildMemEdgesList(Module &M, std::unordered_map<Value*, int>& instToIndex,
                                  std::unordered_map<int, Value*>& indexToInst,
                                  std::list<std::pair<int, int>>& edges) {
  int index = -1;

  auto getIndex = [&instToIndex, &indexToInst, &index](Value* Inst) -> int {
    auto it = instToIndex.find(Inst);
    errs() << "*** " << *Inst << "\n";
    if (it != instToIndex.end()) {
      return it->second;
    } else {
      index++;
      instToIndex[Inst] = index;
      indexToInst[index] = Inst;
      return index;
    }
  };

  for (auto &F : M) {
    if (!F.hasName() || F.isDeclaration()) continue;
    for (auto &BB: F.getBasicBlockList()) {
      for (auto &Inst: BB.getInstList()) {
        if (Inst.isDebugOrPseudoInst()) continue ;
        if (isa<AllocaInst, StoreInst, LoadInst, GetElementPtrInst>(Inst)) {
          int instIndex = getIndex(&Inst);
          for (auto child: Inst.users()) {
            int childIndex = getIndex(child);
            edges.emplace_back(instIndex, childIndex);
          }

          if (auto *storeInst = dyn_cast<StoreInst>(&Inst)) {
            auto storeSrc = storeInst->getValueOperand();
            auto storeDst = storeInst->getPointerOperand();
            int srcIndex = getIndex(storeSrc);
            edges.emplace_back(instIndex, srcIndex);
            int dstIndex = getIndex(storeDst);
            edges.emplace_back(instIndex, dstIndex);
          }

          if (auto *loadInst = dyn_cast<LoadInst>(&Inst)) {
            auto loadSrc = loadInst->getPointerOperand();
            int srcIndex = getIndex(loadSrc);
            edges.emplace_back(instIndex, srcIndex);
          }

          if (auto *gepInst = dyn_cast<GetElementPtrInst>(&Inst)) {
            auto gepSrc = gepInst->getPointerOperand();
            int srcIndex = getIndex(gepSrc);
            edges.emplace_back(instIndex, srcIndex);
          }
        }
      } // instructions
    } // basic blocks
  } // functions

  return index + 1; // number of nodes in the graph
} // buildMemEdgesList

void ReadTrace::parseTraceFiles(std::unordered_map<std::string, double>& minVals,
                                std::unordered_map<std::string, double>& maxVals,
                                std::unordered_map<std::string, mdutils::FloatType::FloatStandard>& valTypes) const {
  for (auto &filename: Filenames) {
    std::cout << "arg: " << filename << std::endl;
    std::string myText;
    std::ifstream MyReadFile(filename);
    while (getline (MyReadFile, myText)) {
      std::string parsed;
      std::stringstream ss(myText);
      getline(ss, parsed, ' ');
      if (parsed != "TAFFO_TRACE") continue;
      getline(ss, parsed, ' ');
      std::string varName = parsed;
      getline(ss, parsed, ' ');
      double varValue = std::stod(parsed);
      getline(ss, parsed, ' ');
      std::string varType = parsed;

//      std::cout << "parsed var: " << varName << " ";
//      std::cout << "parsed val: " << varValue << " ";
//      std::cout << "parsed type: " << varType << std::endl;

      auto minIt = minVals.find(varName);
      if (minIt != minVals.end()) {
        if (minIt->second > varValue) {
          minVals[varName] = varValue;
        }
      } else {
        minVals[varName] = varValue;
      }

      auto maxIt = maxVals.find(varName);
      if (maxIt != maxVals.end()) {
        if (maxIt->second < varValue) {
          maxVals[varName] = varValue;
        }
      } else {
        maxVals[varName] = varValue;
      }

      assert(minVals[varName] <= maxVals[varName]);

      if (valTypes.find(varName) == valTypes.end()) {
        valTypes[varName] = mdutils::FloatType::getFloatStandard(varType);
      }
    }
    MyReadFile.close();
  }
}

PreservedAnalyses ReadTrace::run(llvm::Module &M,
                                       llvm::ModuleAnalysisManager &) {
  bool Changed =  runOnModule(M);

  return (Changed ? llvm::PreservedAnalyses::none()
                  : llvm::PreservedAnalyses::all());
}

#include "TAFFOMath.h"
#include "ArcSinCos.h"
#include "CordicSqrt.h"
#include "HypCORDIC.h"
#include "SinCos.h"
#include "TaffoMathUtil.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/Demangle/Demangle.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include <cassert>
#include <llvm/Support/ErrorHandling.h>
#include <string>
#include <unordered_set>

#define DEBUG_TYPE "taffo-conversion"


using namespace flttofix;
using namespace llvm;
using namespace taffo;


namespace TaffoMath
{

/** Create a new fixedpoint from current float
 * @param cont context used to create instruction
 * @param ref used to access private function
 * @param current_float float to be converted
 * @param match point used as match
 * @param outI instruction returned
 * @param outF fixedpoint returned *
 */
bool createFixedPointFromConst(
    llvm::LLVMContext &cont, FloatToFixed *ref, const double &current_float,
    const FixedPointType &match, llvm::Constant *&outI, FixedPointType &outF

)
{
  flttofix::FloatToFixed::TypeMatchPolicy typepol =
      flttofix::FloatToFixed::TypeMatchPolicy::ForceHint;
  APFloat val(current_float);

  APSInt fixval;

  APFloat tmp(val);

  bool precise = false;
  tmp.convert(APFloatBase::IEEEdouble(), APFloat::rmTowardNegative, &precise);

  double dblval = tmp.convertToDouble();
  int nbits = match.scalarBitsAmt();
  mdutils::Range range(dblval, dblval);
  int minflt = ref->isMaxIntPolicy(typepol) ? -1 : 0;
  mdutils::FPType t =
      taffo::fixedPointTypeFromRange(range, nullptr, nbits, minflt);
  outF = FixedPointType(&t);


  LLVM_DEBUG(dbgs() << "OutF: " << outF << " < Match:" << match << "\n");
  if (outF.scalarFracBitsAmt() < match.scalarFracBitsAmt()) {
    LLVM_DEBUG(dbgs() << "cannot insert " << current_float << " in " << match << "\n");
    return false;
  }


  outF = FixedPointType(match);
  LLVM_DEBUG(dbgs() << "create fixed point from " << current_float << " to "
                    << outF << "\n");

  // create value
  APFloat exp(pow(2.0, outF.scalarFracBitsAmt()));

  exp.convert(val.getSemantics(), APFloat::rmTowardNegative, &precise);

  val.multiply(exp, APFloat::rmTowardNegative);

  fixval = APSInt(match.scalarBitsAmt(), !match.scalarIsSigned());

  APFloat::opStatus cvtres =
      val.convertToInteger(fixval, APFloat::rmTowardNegative, &precise);

  if (cvtres != APFloat::opStatus::opOK) {
    SmallVector<char, 64> valstr;
    val.toString(valstr);
    std::string valstr2(valstr.begin(), valstr.end());
    if (cvtres == APFloat::opStatus::opInexact) {
      LLVM_DEBUG(dbgs() << "ImpreciseConstConversion "
                        << "fixed point conversion of constant " << valstr2
                        << " is not precise\n");
    } else {

      LLVM_DEBUG(dbgs() << "ConstConversionFailed "
                        << " impossible to convert constant " << valstr2
                        << " to fixed point\n");
      return false;
    }
  }

  Type *intty = outF.scalarToLLVMType(cont);
  outI = ConstantInt::get(intty, fixval);
  LLVM_DEBUG(dbgs() << "create int "
                    << (dyn_cast<llvm::Constant>(outI)->dump(), "") << "from "
                    << current_float << "\n");
  return true;
}

Value *addAllocaToStart(FloatToFixed *ref, Function *newfs,
                        llvm::IRBuilder<> &builder, Type *to_alloca,
                        llvm::Value *ArraySize,
                        const llvm::Twine &Name)
{
  auto OldBB = builder.GetInsertBlock();
  LLVM_DEBUG(dbgs() << "Insert alloca inst\nOld basic block: " << OldBB << "\n");
  builder.SetInsertPoint(&(newfs->getEntryBlock()),
                         (newfs->getEntryBlock()).getFirstInsertionPt());
  Value *pointer_to_alloca = builder.CreateAlloca(to_alloca, ArraySize, Name);
  LLVM_DEBUG(dbgs() << "New Alloca: " << pointer_to_alloca << "\n");
  builder.SetInsertPoint(OldBB);
  return pointer_to_alloca;
}

void getFixedFromRet(FloatToFixed *ref, Function *oldf,
                     FixedPointType &fxpret, bool &found)
{
  for (auto i : oldf->users()) {
    if (isa<llvm::CallInst>(i)) {
      llvm::CallInst *callInst = dyn_cast<llvm::CallInst>(i);
      if (ref->hasInfo(callInst)) {
        fxpret = ref->valueInfo(callInst)->fixpType;
        LLVM_DEBUG(dbgs() << "\nReturn type: Scalar bits "
                          << fxpret.scalarBitsAmt() << "Fractional bits"
                          << fxpret.scalarFracBitsAmt() << "\n");
        found = true;
        return;
      }
    }
  }
  LLVM_DEBUG(dbgs() << "Fix not founds for return "
                    << "\n");

  found = false;
}

void getFixedFromArg(FloatToFixed *ref, Function *oldf,
                     FixedPointType &fxparg, int n, bool &found)
{
  LLVM_DEBUG(dbgs() << *oldf << "\n");

  for (auto arg = oldf->arg_begin(); arg != oldf->arg_end(); ++arg) {
    if (n == 0) {

      LLVM_DEBUG(dbgs() << "Try n: " << n << "\n");

      if (ref->hasInfo(arg)) {
        LLVM_DEBUG(dbgs() << "arg: "
                          << "\n");
        fxparg = ref->valueInfo(arg)->fixpType;
        LLVM_DEBUG(dbgs() << "\nReturn arg: Scalar bits "
                          << fxparg.scalarBitsAmt() << "Fractional bits"
                          << fxparg.scalarFracBitsAmt() << "\n");
        found = true;
        return;
      }
    }
    --n;
  }
  LLVM_DEBUG(dbgs() << "Fix not founded from for arguments"
                    << "\n");
  found = false;
}

llvm::GlobalVariable *
createGlobalConst(llvm::Module *module, llvm::StringRef Name, llvm::Type *Ty,
                  Constant *initializer, unsigned int alignment)
{

  module->getOrInsertGlobal(Name, Ty);
  auto global = module->getGlobalVariable(Name);
  if (!global->hasInitializer()) {
    global->setInitializer(initializer);
    global->setConstant(true);
    if (alignment > 1)
      global->setAlignment(llvm::Align(alignment));
  }
  return global;
}

} // namespace TaffoMath


namespace flttofix
{

void createStub(Function *OldFunc)
{
  auto BB = BasicBlock::Create(OldFunc->getContext(), OldFunc->getName() + ".entry", OldFunc);
  IRBuilder<> builder(BB, BB->getFirstInsertionPt());
  Value *V;
  if (OldFunc->getReturnType()->isFloatingPointTy()) {
    V = ConstantFP::get(OldFunc->getReturnType(), 0);
    builder.CreateRet(V);
    return;

  } else if (OldFunc->getReturnType()->isIntegerTy()) {
    V = ConstantInt::get(OldFunc->getReturnType(), 0);
    builder.CreateRet(V);
    return;
  }
  llvm_unreachable("return not handle");
}


bool partialSpecialCall(
    llvm::Function *newf, bool &foundRet, flttofix::FixedPointType &fxpret)
{
  Module *m = newf->getParent();
  BasicBlock *where = &(newf->getEntryBlock());
  IRBuilder<> builder(where, where->getFirstInsertionPt());
  auto end = BasicBlock::Create(m->getContext(), "end", newf);
  auto trap = Intrinsic::getDeclaration(m, Intrinsic::trap);
  builder.CreateCall(trap);
  builder.CreateBr(end);
  builder.SetInsertPoint(end);
  if (newf->getReturnType()->isFloatingPointTy()) {
    builder.CreateRet(ConstantFP::get(newf->getReturnType(), 1212.0f));
  } else {
    builder.CreateRet(ConstantInt::get(newf->getReturnType(), 1212));
  }
  LLVM_DEBUG(dbgs() << "Not handled\n");
  return false;
}


/**
 * Create the fma function.
 *
 * @param ref the FloatToFixed object
 * @param newfs the new function
 * @param oldf the old function
 * @return true if the function was created successfully, false otherwise
 */
bool createFma(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  newfs->deleteBody();
  Module *M = oldf->getParent();
  // Retrieve context used in later instruction
  llvm::LLVMContext &cont(oldf->getContext());
  DataLayout dataLayout(M);
  LLVM_DEBUG(dbgs() << "\nGet Context " << &cont << "\n");
  // Get first basic block of function
  BasicBlock::Create(cont, "Entry", newfs);
  BasicBlock *where = &(newfs->getEntryBlock());
  LLVM_DEBUG(dbgs() << "\nGet entry point " << where);
  IRBuilder<> builder(where, where->getFirstInsertionPt());

  // get return type fixed point
  flttofix::FixedPointType fxpret;
  // get arguments fixed point
  flttofix::FixedPointType fxparg1;
  flttofix::FixedPointType fxparg2;
  flttofix::FixedPointType fxparg3;

  bool foundRet = false;
  bool foundArg1 = false;
  bool foundArg2 = false;
  bool foundArg3 = false;

  TaffoMath::getFixedFromRet(ref, oldf, fxpret, foundRet);
  TaffoMath::getFixedFromArg(ref, oldf, fxparg1, 0, foundArg1);
  TaffoMath::getFixedFromArg(ref, oldf, fxparg2, 1, foundArg2);
  TaffoMath::getFixedFromArg(ref, oldf, fxparg3, 2, foundArg3);

  if (!foundRet || !foundArg1 || !foundArg2 || !foundArg3) {
    LLVM_DEBUG(dbgs() << "Return or argument not found\n");
    return partialSpecialCall(newfs, foundRet, fxpret);
  }

  auto int_type = fxparg1.scalarToLLVMType(cont);

  // Allocate space for the arguments
  Value *arg1_ptr = builder.CreateAlloca(int_type, nullptr, "arg1");
  builder.CreateStore(newfs->getArg(0), arg1_ptr);

  Value *arg2_ptr = builder.CreateAlloca(int_type, nullptr, "arg2");
  builder.CreateStore(newfs->getArg(1), arg2_ptr);

  Value *arg3_ptr = builder.CreateAlloca(int_type, nullptr, "arg3");
  builder.CreateStore(newfs->getArg(2), arg3_ptr);

  // handle unsigned arg1
  if (!fxparg1.scalarIsSigned()) {
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg1_ptr), arg1_ptr), ConstantInt::get(int_type, 1)), arg1_ptr);
    fxparg1.scalarFracBitsAmt() = fxparg1.scalarFracBitsAmt() - 1;
    fxparg1.scalarIsSigned() = true;
  }
  // handle unsigned arg2
  if (!fxparg2.scalarIsSigned()) {
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg2_ptr), arg2_ptr), ConstantInt::get(int_type, 1)), arg2_ptr);
    fxparg2.scalarFracBitsAmt() = fxparg2.scalarFracBitsAmt() - 1;
    fxparg2.scalarIsSigned() = true;
  }
  // handle unsigned arg3
  if (!fxparg3.scalarIsSigned()) {
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg3_ptr), arg3_ptr), ConstantInt::get(int_type, 1)), arg3_ptr);
    fxparg3.scalarFracBitsAmt() = fxparg3.scalarFracBitsAmt() - 1;
    fxparg3.scalarIsSigned() = true;
  }

  // Allocate space for the result
  Value *result_ptr = builder.CreateAlloca(int_type, nullptr, "result");

  // ----------------------------------------------------
  // Create the multiplication function that is needed for the arg1*arg2 part of the fma
  std::string mul_function_name("llvm.smul.fix.i");
  mul_function_name.append(std::to_string(fxpret.scalarToLLVMType(cont)->getScalarSizeInBits()));

  Function *function_mul = M->getFunction(mul_function_name);
  if (function_mul == nullptr) {
    // Define the function if it doesn't exist
    std::vector<llvm::Type *> fun_arguments;
    fun_arguments.push_back(
        fxpret.scalarToLLVMType(cont));
    fun_arguments.push_back(
        fxpret.scalarToLLVMType(cont));
    fun_arguments.push_back(Type::getInt32Ty(cont));
    FunctionType *fun_type = FunctionType::get(
        fxpret.scalarToLLVMType(cont), fun_arguments, false);
    function_mul = llvm::Function::Create(fun_type, GlobalValue::ExternalLinkage,
                                          mul_function_name, M);
  }

  LLVM_DEBUG(dbgs() << "Mul function: ");
  function_mul->print(dbgs());
  LLVM_DEBUG(dbgs() << "\n");

  // Adapt the fractional bits of the arguments to the fractional bits of the result
  if (fxparg1.scalarFracBitsAmt() > fxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(arg1_ptr), arg1_ptr), fxparg1.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), arg1_ptr);
  } else if (fxparg1.scalarFracBitsAmt() < fxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(arg1_ptr), arg1_ptr), fxpret.scalarFracBitsAmt() - fxparg1.scalarFracBitsAmt()), arg1_ptr);
  }
  if (fxparg2.scalarFracBitsAmt() > fxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(arg2_ptr), arg2_ptr), fxparg2.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), arg2_ptr);
  } else if (fxparg2.scalarFracBitsAmt() < fxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(arg2_ptr), arg2_ptr), fxpret.scalarFracBitsAmt() - fxparg2.scalarFracBitsAmt()), arg2_ptr);
  }
  if (fxparg3.scalarFracBitsAmt() > fxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(arg3_ptr), arg3_ptr), fxparg3.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), arg3_ptr);
  } else if (fxparg3.scalarFracBitsAmt() < fxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(arg3_ptr), arg3_ptr), fxpret.scalarFracBitsAmt() - fxparg3.scalarFracBitsAmt()), arg3_ptr);
  }

  // Perform the multiplication call (arg1*arg2)
  auto result_tmp = builder.CreateCall(
      function_mul,
      {
          builder.CreateLoad(getElementTypeFromValuePointer(arg1_ptr), arg1_ptr, "arg1"),
          builder.CreateLoad(getElementTypeFromValuePointer(arg2_ptr), arg2_ptr, "arg2"),
          llvm::ConstantInt::get(fxpret.scalarToLLVMType(cont), fxpret.scalarFracBitsAmt()) // Ensure this matches the expected type
      });

  // Store the result of the multiplication in the result pointer
  builder.CreateStore(result_tmp, result_ptr);

  // Add arg1 * arg2 to arg3 and store it in result_ptr
  builder.CreateStore(builder.CreateAdd(
                          builder.CreateLoad(getElementTypeFromValuePointer(result_ptr), result_ptr),
                          builder.CreateLoad(getElementTypeFromValuePointer(arg3_ptr), arg3_ptr)),
                      result_ptr);

  builder.CreateRet(builder.CreateLoad(getElementTypeFromValuePointer(result_ptr), result_ptr));
  return true;
}


/*
Doesn't work look at TAFFO/lib/RangeAnalysis/TaffoVRA/RangeOperationsCallWhitelist.cpp
*/
bool createFmax(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  newfs->deleteBody();
  Module *M = oldf->getParent();
  // Retrieve context used in later instruction
  llvm::LLVMContext &cont(oldf->getContext());
  DataLayout dataLayout(M);
  LLVM_DEBUG(dbgs() << "\nGet Context " << &cont << "\n");
  // Get first basic block of function
  BasicBlock::Create(cont, "Entry", newfs);
  BasicBlock *where = &(newfs->getEntryBlock());
  LLVM_DEBUG(dbgs() << "\nGet entry point " << where);
  IRBuilder<> builder(where, where->getFirstInsertionPt());

  // get return type fixed point
  flttofix::FixedPointType fxpret;
  // get arguments fixed point
  flttofix::FixedPointType fxparg1;
  flttofix::FixedPointType fxparg2;

  bool foundRet = false;
  bool foundArg1 = false;
  bool foundArg2 = false;

  // Get the fixed point type of the return value
  TaffoMath::getFixedFromRet(ref, oldf, fxpret, foundRet);
  // Get the fixed point type of the arguments
  TaffoMath::getFixedFromArg(ref, oldf, fxparg1, 0, foundArg1);
  TaffoMath::getFixedFromArg(ref, oldf, fxparg2, 1, foundArg2);

  if (!foundRet || !foundArg1 || !foundArg2) {
    LLVM_DEBUG(dbgs() << "Return or argument not found\n");
    return partialSpecialCall(newfs, foundRet, fxpret);
  }

  auto int_type = fxpret.scalarToLLVMType(cont);

  // Allocate space for the arguments
  Value *arg1_ptr = builder.CreateAlloca(int_type, nullptr, "arg1");
  builder.CreateStore(newfs->getArg(0), arg1_ptr);

  Value *arg2_ptr = builder.CreateAlloca(int_type, nullptr, "arg2");
  builder.CreateStore(newfs->getArg(1), arg2_ptr);

  // handle unsigned arg1
  if (!fxparg1.scalarIsSigned()) {
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg1_ptr), arg1_ptr), ConstantInt::get(int_type, 1)), arg1_ptr);
    fxparg1.scalarFracBitsAmt() = fxparg1.scalarFracBitsAmt() - 1;
    fxparg1.scalarIsSigned() = true;
  }
  // handle unsigned arg2
  if (!fxparg2.scalarIsSigned()) {
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg2_ptr), arg2_ptr), ConstantInt::get(int_type, 1)), arg2_ptr);
    fxparg2.scalarFracBitsAmt() = fxparg2.scalarFracBitsAmt() - 1;
    fxparg2.scalarIsSigned() = true;
  }

  // Allocate space for the result
  Value *result_ptr = builder.CreateAlloca(int_type, nullptr, "result");

  // Adapt the fractional bits of the arguments to the fractional bits of the result
  if (fxparg1.scalarFracBitsAmt() > fxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(arg1_ptr), arg1_ptr), fxparg1.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), arg1_ptr);
  } else if (fxparg1.scalarFracBitsAmt() < fxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(arg1_ptr), arg1_ptr), fxpret.scalarFracBitsAmt() - fxparg1.scalarFracBitsAmt()), arg1_ptr);
  }
  if (fxparg2.scalarFracBitsAmt() > fxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(arg2_ptr), arg2_ptr), fxparg2.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), arg2_ptr);
  } else if (fxparg2.scalarFracBitsAmt() < fxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(arg2_ptr), arg2_ptr), fxpret.scalarFracBitsAmt() - fxparg2.scalarFracBitsAmt()), arg2_ptr);
  }

  // Perform the comparison
  auto cmp = builder.CreateICmpSGT(builder.CreateLoad(getElementTypeFromValuePointer(arg1_ptr), arg1_ptr), builder.CreateLoad(getElementTypeFromValuePointer(arg2_ptr), arg2_ptr));

  // Store the result of the comparison in the result pointer
  builder.CreateStore(builder.CreateSelect(cmp, builder.CreateLoad(getElementTypeFromValuePointer(arg1_ptr), arg1_ptr), builder.CreateLoad(getElementTypeFromValuePointer(arg2_ptr), arg2_ptr)), result_ptr);

  builder.CreateRet(builder.CreateLoad(getElementTypeFromValuePointer(result_ptr), result_ptr));
  return true;
}

/**
 * Create the copysign function.
 *
 * @param ref the FloatToFixed object
 * @param newfs the new function
 * @param oldf the old function
 * @return true if the function was created successfully, false otherwise
 */
bool createCopysign(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  newfs->deleteBody();
  Module *M = oldf->getParent();
  // Retrieve context used in later instruction
  llvm::LLVMContext &cont(oldf->getContext());
  DataLayout dataLayout(M);
  LLVM_DEBUG(dbgs() << "\nGet Context " << &cont << "\n");
  // Get first basic block of function
  BasicBlock::Create(cont, "Entry", newfs);
  BasicBlock *where = &(newfs->getEntryBlock());
  LLVM_DEBUG(dbgs() << "\nGet entry point " << where);
  IRBuilder<> builder(where, where->getFirstInsertionPt());

  // get return type fixed point
  flttofix::FixedPointType fxpret;
  // get arguments fixed point
  flttofix::FixedPointType fxparg1;
  flttofix::FixedPointType fxparg2;

  bool foundRet = false;
  bool foundArg1 = false;
  bool foundArg2 = false;

  // Get the fixed point type of the return value
  TaffoMath::getFixedFromRet(ref, oldf, fxpret, foundRet);
  // Get the fixed point type of the arguments
  TaffoMath::getFixedFromArg(ref, oldf, fxparg1, 0, foundArg1);
  TaffoMath::getFixedFromArg(ref, oldf, fxparg2, 1, foundArg2);

  if (!foundRet || !foundArg1 || !foundArg2) {
    LLVM_DEBUG(dbgs() << "Return or argument not found\n");
    return partialSpecialCall(newfs, foundRet, fxpret);
  }

  auto int_type = fxpret.scalarToLLVMType(cont);

  // Allocate space for the arguments
  Value *arg1_ptr = builder.CreateAlloca(int_type, nullptr, "arg1");
  builder.CreateStore(newfs->getArg(0), arg1_ptr);

  Value *arg2_ptr = builder.CreateAlloca(int_type, nullptr, "arg2");
  builder.CreateStore(newfs->getArg(1), arg2_ptr);

  // Allocate space for the result
  Value *result_ptr = builder.CreateAlloca(int_type, nullptr, "result");

  // handle unsigned arg1
  if (!fxparg1.scalarIsSigned()) {
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg1_ptr), arg1_ptr), ConstantInt::get(int_type, 1)), arg1_ptr);
    fxparg1.scalarFracBitsAmt() = fxparg1.scalarFracBitsAmt() - 1;
    fxparg1.scalarIsSigned() = true;
  }
  // handle unsigned arg2
  if (!fxparg2.scalarIsSigned()) {
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg2_ptr), arg2_ptr), ConstantInt::get(int_type, 1)), arg2_ptr);
    fxparg2.scalarFracBitsAmt() = fxparg2.scalarFracBitsAmt() - 1;
    fxparg2.scalarIsSigned() = true;
  }

  // Generate strings for constants names
  std::string S_arg1_point = "." + std::to_string(fxparg1.scalarFracBitsAmt());

  // Pointer to zero in the internal fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_arg(fxparg1);

  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, fxparg1, zero_arg.value, zero_arg.fpt);

  zero_arg.value = TaffoMath::createGlobalConst(
      M, "zero_arg" + S_arg1_point, zero_arg.fpt.scalarToLLVMType(cont), zero_arg.value,
      dataLayout.getPrefTypeAlignment(zero_arg.fpt.scalarToLLVMType(cont)));

  // Calculate copysign

  // Load the zero value
  auto zero_value = builder.CreateLoad(getElementTypeFromValuePointer(zero_arg.value), zero_arg.value);

  // Check the sign of the arg2
  Value *check_sign = builder.CreateICmpSLE(
      builder.CreateLoad(getElementTypeFromValuePointer(arg2_ptr), arg2_ptr),
      zero_value // Confronta con zero per verificare il segno negativo
  );

  // result = check_sign ? -arg1 : arg1
  auto result_value = builder.CreateSelect(
      check_sign,
      builder.CreateSub(
          zero_value,
          builder.CreateLoad(getElementTypeFromValuePointer(arg1_ptr), arg1_ptr)),
      builder.CreateLoad(getElementTypeFromValuePointer(arg1_ptr), arg1_ptr));

  // Store the result
  builder.CreateStore(result_value, result_ptr);

  // Return the result
  builder.CreateRet(builder.CreateLoad(getElementTypeFromValuePointer(result_ptr), result_ptr));
  return true;
}


bool createAbs(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  LLVM_DEBUG(dbgs() << "*********** " << __FUNCTION__ << "\n");

  // Boilerplate
  llvm::LLVMContext &cont(oldf->getContext());
  DataLayout dataLayout(oldf->getParent());

  // Get the types of the arguments and the return value
  auto arg_type = newfs->getArg(0)->getType();
  auto ret_type = newfs->getReturnType();

  LLVM_DEBUG(dbgs() << "\nThe argument type is: " << *arg_type);
  LLVM_DEBUG(dbgs() << "\nThe return type is: " << *ret_type);

  BasicBlock::Create(cont, "Entry", newfs);
  BasicBlock *where = &(newfs->getEntryBlock());
  IRBuilder<> builder(where, where->getFirstInsertionPt());

  // If the argument is not signed, return it as it is.
  if (ref->hasInfo(oldf->getArg(0)) && !(ref->valueInfo(oldf->getArg(0))->fixpType.scalarIsSigned())) {
    builder.CreateRet(newfs->getArg(0));
    return true;
  }

  // Create a bitcast of the argument to an integer type
  LLVM_DEBUG(dbgs() << "\nGet insertion\n");
  auto *inst = builder.CreateBitCast(newfs->getArg(0), llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()));
  LLVM_DEBUG(dbgs() << "\nGet bitcast\n");

  // Create a select instruction to handle the sign of the argument
  inst = builder.CreateSelect(
      // Compare for equality (1) and (2)
      builder.CreateICmpEQ(
          // (1): The result of shifting right the argument by the number of bits in the argument minus 1
          builder.CreateLShr(inst, arg_type->getScalarSizeInBits() - 1),
          // (2): The constant 1
          llvm::ConstantInt::get(llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), 1)),
      // If true (i.e., the argument is negative), return (3)
      builder.CreateBitCast(
          // (3): Create subtraction of (5) from (4)
          builder.CreateSub(
              // (4): The constant 0
              llvm::ConstantInt::get(llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), 0),
              // (5): The argument
              inst),
          arg_type),
      // If false (i.e., the argument is positive), return the argument as-is
      inst);

  LLVM_DEBUG(dbgs() << "Abs logic created.\n");

  // Cast the integer to the return type
  if (arg_type->isFloatingPointTy() && ret_type->isFloatingPointTy()) {
    inst = builder.CreateFPCast(inst, ret_type);
  } else if (arg_type->isFloatingPointTy() && ret_type->isIntegerTy()) {
    inst = builder.CreateFPToSI(inst, ret_type);
  } else if (arg_type->isIntegerTy() && ret_type->isFloatingPointTy()) {
    inst = builder.CreateSIToFP(inst, ret_type);
  } else if (arg_type->isIntegerTy() && ret_type->isIntegerTy()) {
    inst = builder.CreateIntCast(inst, ret_type, true);
  }

  LLVM_DEBUG(dbgs() << "The result was casted to the return type.\n");

  builder.CreateRet(inst);
}

/**
 * Create the ceil function.
 *
 * @param ref the FloatToFixed object
 * @param newfs the new function
 * @param oldf the old function
 * @return true if the function was created successfully, false otherwise
 */
bool createCeil(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  LLVM_DEBUG(dbgs() << "*********** " << __FUNCTION__ << "\n");

  newfs->deleteBody();

  // Boilerplate
  llvm::LLVMContext &cont(oldf->getContext());
  DataLayout dataLayout(oldf->getParent());

  // Get the types of the arguments and the return value
  auto arg_type = newfs->getArg(0)->getType();
  auto ret_type = newfs->getReturnType();

  LLVM_DEBUG(dbgs() << "The argument type is: " << (*arg_type) << "\n");
  LLVM_DEBUG(dbgs() << "The return type is: " << (*ret_type) << "\n");

  BasicBlock::Create(cont, "Entry", newfs);
  BasicBlock *where = &(newfs->getEntryBlock());
  IRBuilder<> builder(where, where->getFirstInsertionPt());

  // Create a bitcast of the argument to an integer type
  auto *inst = builder.CreateBitCast(newfs->getArg(0), llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()));

  LLVM_DEBUG(dbgs() << "Created bitcast with size " << arg_type->getPrimitiveSizeInBits() << " bits.\n");

  inst = builder.CreateSelect(
      // Compare:
      builder.CreateICmpEQ(
          // The fractional part of the argument
          builder.CreateShl(inst, ref->valueInfo(oldf->getArg(0))->fixpType.scalarIntegerBitsAmt()),
          // The constant 0
          llvm::ConstantInt::get(llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), 0)),
      // If true (fractional part was already 0), return the argument
      inst,
      // If false (fractional part was nonzero): shift:
      builder.CreateShl(
          // The sum of:
          builder.CreateAdd(
              // The right shift of the argument by the fractional part, i.e. the fractional part is removed
              builder.CreateLShr(inst, ref->valueInfo(oldf->getArg(0))->fixpType.scalarFracBitsAmt()),
              // To the constant 1. This is needed because the number is encoded in two's complement
              llvm::ConstantInt::get(llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), 1)),
          // By the amount of bits in fractional part. At this point, the fractional part is removed
          ref->valueInfo(oldf->getArg(0))->fixpType.scalarFracBitsAmt()));

  LLVM_DEBUG(dbgs() << "Ceil logic created.\n");

  // Cast the integer to the return type
  if (arg_type->isFloatingPointTy() && ret_type->isFloatingPointTy()) {
    inst = builder.CreateFPCast(inst, ret_type);
  } else if (arg_type->isFloatingPointTy() && ret_type->isIntegerTy()) {
    inst = builder.CreateFPToSI(inst, ret_type);
  } else if (arg_type->isIntegerTy() && ret_type->isFloatingPointTy()) {
    inst = builder.CreateSIToFP(inst, ret_type);
  } else if (arg_type->isIntegerTy() && ret_type->isIntegerTy()) {
    inst = builder.CreateIntCast(inst, ret_type, true);
  }
  builder.CreateRet(inst);

  return true;
}

/**
 * Create the floor function.
 *
 * @param ref the FloatToFixed object
 * @param newfs the new function
 * @param oldf the old function
 * @return true if the function was created successfully, false otherwise
 */
bool createFloor(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  LLVM_DEBUG(dbgs() << "*********** " << __FUNCTION__ << "\n");

  newfs->deleteBody();

  // Boilerplate
  llvm::LLVMContext &cont(oldf->getContext());
  DataLayout dataLayout(oldf->getParent());

  // Get the types of the arguments and the return value
  auto arg_type = newfs->getArg(0)->getType();
  auto ret_type = newfs->getReturnType();

  LLVM_DEBUG(dbgs() << "The argument type is: " << (*arg_type) << "\n");
  LLVM_DEBUG(dbgs() << "The return type is: " << (*ret_type) << "\n");

  BasicBlock::Create(cont, "Entry", newfs);
  BasicBlock *where = &(newfs->getEntryBlock());
  IRBuilder<> builder(where, where->getFirstInsertionPt());

  // Create a bitcast of the argument to an integer type
  auto *inst = builder.CreateBitCast(newfs->getArg(0), llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()));

  LLVM_DEBUG(dbgs() << "Created bitcast with size " << arg_type->getPrimitiveSizeInBits() << " bits.\n");

  inst = builder.CreateSelect(
      // Compare:
      builder.CreateICmpEQ(
          // The fractional part of the argument
          builder.CreateShl(inst, ref->valueInfo(oldf->getArg(0))->fixpType.scalarIntegerBitsAmt()),
          // The constant 0
          llvm::ConstantInt::get(llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), 0)),
      // If true (fractional part was already 0), return the argument
      inst,
      // If false (fractional part was nonzero):
      // Shift left:
      builder.CreateShl(
          // The right shift of the argument by the fractional part
          builder.CreateLShr(inst, ref->valueInfo(oldf->getArg(0))->fixpType.scalarFracBitsAmt()),
          // By the amount of bits in fractional part. At this point, the fractional part is removed
          ref->valueInfo(oldf->getArg(0))->fixpType.scalarFracBitsAmt()));

  // Note that we need not do anything else because our number is be encoded in two's complement.

  LLVM_DEBUG(dbgs() << "Floor logic created.\n");

  // Cast the integer to the return type
  if (arg_type->isFloatingPointTy() && ret_type->isFloatingPointTy()) {
    inst = builder.CreateFPCast(inst, ret_type);
  } else if (arg_type->isFloatingPointTy() && ret_type->isIntegerTy()) {
    inst = builder.CreateFPToSI(inst, ret_type);
  } else if (arg_type->isIntegerTy() && ret_type->isFloatingPointTy()) {
    inst = builder.CreateSIToFP(inst, ret_type);
  } else if (arg_type->isIntegerTy() && ret_type->isIntegerTy()) {
    inst = builder.CreateIntCast(inst, ret_type, true);
  }
  builder.CreateRet(inst);

  return true;
}

/**
 * Create the trunc function.
 *
 * @param ref the FloatToFixed object
 * @param newfs the new function
 * @param oldf the old function
 * @return true if the function was created successfully, false otherwise
 */
bool createTrunc(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  LLVM_DEBUG(dbgs() << "*********** " << __FUNCTION__ << "\n");

  newfs->deleteBody();

  llvm::LLVMContext &cont(oldf->getContext());
  DataLayout dataLayout(oldf->getParent());

  // Get the types of the arguments and the return value
  auto arg_type = newfs->getArg(0)->getType();
  auto ret_type = newfs->getReturnType();
  // Get return type fixed point
  flttofix::FixedPointType fxpret;
  flttofix::FixedPointType fxparg;
  bool foundRet = false;
  bool foundArg = false;
  TaffoMath::getFixedFromRet(ref, oldf, fxpret, foundRet);
  // Get argument fixed point
  TaffoMath::getFixedFromArg(ref, oldf, fxparg, 0, foundArg);
  if (!foundRet || !foundArg) {
    LLVM_DEBUG(dbgs() << "Return or argument not found\n");
    return partialSpecialCall(newfs, foundRet, fxpret);
  }

  LLVM_DEBUG(dbgs() << "The argument type is: " << (*arg_type) << "\n");
  LLVM_DEBUG(dbgs() << "The return type is: " << (*ret_type) << "\n");

  BasicBlock::Create(cont, "Entry", newfs);
  BasicBlock *where = &(newfs->getEntryBlock());
  IRBuilder<> builder(where, where->getFirstInsertionPt());

  // Create a bitcast of the argument to an integer type
  auto *inst = builder.CreateBitCast(newfs->getArg(0), llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()));

  LLVM_DEBUG(dbgs() << "Created bitcast with size " << arg_type->getPrimitiveSizeInBits() << " bits.\n");

  // If signed:
  if (fxparg.scalarIsSigned()) {
    inst = builder.CreateSelect(
        // Compare:
        builder.CreateICmpEQ(
            // The fractional part of the argument
            builder.CreateShl(inst, ref->valueInfo(oldf->getArg(0))->fixpType.scalarIntegerBitsAmt(), "frac_part"),
            // The constant 0
            llvm::ConstantInt::get(llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), 0), "frac_part_is_zero"),
        // If true (fractional part was already 0), return the argument
        inst,
        // If false (fractional part was nonzero):
        builder.CreateSelect(
            // Compare:
            builder.CreateICmpEQ(
                // The sign (i.e., the most significant bit) of the argument
                builder.CreateLShr(inst, arg_type->getScalarSizeInBits() - 1, "sign_bit"),
                // The constant 0
                llvm::ConstantInt::get(llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), 0), "sign_bit_is_zero"),
            // If true (the argument is positive): shift left:
            builder.CreateShl(
                // The right shift of the argument by the fractional part, i.e. the fractional part is removed
                builder.CreateLShr(inst, ref->valueInfo(oldf->getArg(0))->fixpType.scalarFracBitsAmt(), "integer_part"),
                // By the amount of bits in fractional part. At this point, the fractional part is removed
                ref->valueInfo(oldf->getArg(0))->fixpType.scalarFracBitsAmt(), "arg_final_if_positive"),
            // If false (the argument is negative): shift right:
            builder.CreateShl(
                // Add:
                builder.CreateAdd(
                    // The right shift of the argument by the fractional part, i.e. the fractional part is removed
                    builder.CreateLShr(inst, ref->valueInfo(oldf->getArg(0))->fixpType.scalarFracBitsAmt(), "integer_part"),
                    // To the constant 1. This is needed because the number is encoded in two's complement
                    llvm::ConstantInt::get(llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), 1), "arg_plus_one"),
                // By the amount of bits in fractional part. At this point, the fractional part is removed
                ref->valueInfo(oldf->getArg(0))->fixpType.scalarFracBitsAmt(), "arg_final_if_negative"),
            "arg_final"),
        "return_value");

  } else {
    // If unsigned skip positive/negative check
    inst = builder.CreateSelect(
        // Compare:
        builder.CreateICmpEQ(
            // The fractional part of the argument
            builder.CreateShl(inst, ref->valueInfo(oldf->getArg(0))->fixpType.scalarIntegerBitsAmt(), "frac_part"),
            // The constant 0
            llvm::ConstantInt::get(llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), 0), "frac_part_is_zero"),
        // If true (fractional part was already 0), return the argument
        inst,
        // If false (fractional part was nonzero):
        builder.CreateShl(
            // The right shift of the argument by the fractional part, i.e. the fractional part is removed
            builder.CreateLShr(inst, ref->valueInfo(oldf->getArg(0))->fixpType.scalarFracBitsAmt(), "integer_part"),
            // By the amount of bits in fractional part. At this point, the fractional part is removed
            ref->valueInfo(oldf->getArg(0))->fixpType.scalarFracBitsAmt(), "arg_final"),
        "return_value");
  }

  LLVM_DEBUG(dbgs() << "Trunc logic created.\n");

  // Cast the integer to the return type
  if (arg_type->isFloatingPointTy() && ret_type->isFloatingPointTy()) {
    inst = builder.CreateFPCast(inst, ret_type);
  } else if (arg_type->isFloatingPointTy() && ret_type->isIntegerTy()) {
    inst = builder.CreateFPToSI(inst, ret_type);
  } else if (arg_type->isIntegerTy() && ret_type->isFloatingPointTy()) {
    inst = builder.CreateSIToFP(inst, ret_type);
  } else if (arg_type->isIntegerTy() && ret_type->isIntegerTy()) {
    inst = builder.CreateIntCast(inst, ret_type, true);
  }
  builder.CreateRet(inst);

  return true;
}

/**
 * Create the round function.
 *
 * @param ref the FloatToFixed object
 * @param newfs the new function
 * @param oldf the old function
 * @return true if the function was created successfully, false otherwise
 */
bool createRound(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  LLVM_DEBUG(dbgs() << "*********** " << __FUNCTION__ << "\n");

  newfs->deleteBody();

  llvm::LLVMContext &cont(oldf->getContext());
  DataLayout dataLayout(oldf->getParent());

  // Get the types of the arguments and the return value
  auto arg_type = newfs->getArg(0)->getType();
  auto ret_type = newfs->getReturnType();
  // Get return type fixed point
  flttofix::FixedPointType fxpret;
  flttofix::FixedPointType fxparg;
  bool foundRet = false;
  bool foundArg = false;
  TaffoMath::getFixedFromRet(ref, oldf, fxpret, foundRet);
  // Get argument fixed point
  TaffoMath::getFixedFromArg(ref, oldf, fxparg, 0, foundArg);
  if (!foundRet || !foundArg) {
    LLVM_DEBUG(dbgs() << "Return or argument not found\n");
    return partialSpecialCall(newfs, foundRet, fxpret);
  }

  LLVM_DEBUG(dbgs() << "The argument type is: " << (*arg_type) << "\n");
  LLVM_DEBUG(dbgs() << "The return type is: " << (*ret_type) << "\n");

  BasicBlock::Create(cont, "Entry", newfs);
  BasicBlock *where = &(newfs->getEntryBlock());
  IRBuilder<> builder(where, where->getFirstInsertionPt());

  // Create a bitcast of the argument to an integer type
  Value *result = builder.CreateBitCast(newfs->getArg(0), llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), "initial_arg");

  LLVM_DEBUG(dbgs() << "Created bitcast with size " << arg_type->getPrimitiveSizeInBits() << " bits.\n");

  auto frac_part = builder.CreateShl(result, ref->valueInfo(oldf->getArg(0))->fixpType.scalarIntegerBitsAmt(), "frac_part");
  auto fracPartIsZero = builder.CreateICmpEQ(
      frac_part,
      llvm::ConstantInt::get(llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), 0), "frac_part_is_zero");

  auto fracPartIsGreaterOrEqualThanHalf = builder.CreateICmpUGE(
      frac_part,
      llvm::ConstantInt::get(llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), 1 << (arg_type->getScalarSizeInBits() - 1)), "frac_part_is_greater_equal_half");

  Value *integer_part = builder.CreateAShr(result, ref->valueInfo(oldf->getArg(0))->fixpType.scalarFracBitsAmt(), "integer_part");

  Value *result_arg_is_positive_and_frac_part_is_less_than_half = integer_part;
  Value *result_arg_if_frac_part_is_greater_than_half = builder.CreateAdd(integer_part, llvm::ConstantInt::get(llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), 1), "result_if_frac_part_is_greater_than_half");

  Value *result_if_frac_part_is_nonzero;
  // If signed:
  if (fxparg.scalarIsSigned()) {


    auto argIsPositive = builder.CreateICmpSGE(
        integer_part,
        llvm::ConstantInt::get(llvm::Type::getIntNTy(cont, arg_type->getPrimitiveSizeInBits()), 0), "arg_is_positive");

    /*
      If arg is positive and fractional part is less than half, OR if arg is negative and fractional part is greater than half,
      then the result is the integer part of the argument.
    */
    Value *result_is_negative_and_frac_part_is_less_than_half = integer_part;

    // Choose the result based on the sign of the argument and the fractional part
    result_if_frac_part_is_nonzero = builder.CreateSelect(argIsPositive,
                                                                 builder.CreateSelect(fracPartIsGreaterOrEqualThanHalf, result_arg_if_frac_part_is_greater_than_half, result_arg_is_positive_and_frac_part_is_less_than_half, "result_if_positive"),
                                                                 builder.CreateSelect(fracPartIsGreaterOrEqualThanHalf, result_arg_if_frac_part_is_greater_than_half, result_is_negative_and_frac_part_is_less_than_half, "result_if_negative"), "result_if_frac_part_is_nonzero_integer_part");
  } else {
    // If unsigned skip positive/negative check
    result_if_frac_part_is_nonzero = builder.CreateSelect(fracPartIsGreaterOrEqualThanHalf, result_arg_if_frac_part_is_greater_than_half, integer_part, "result_if_frac_part_is_greater_than_half");
  }
  
  // Shift the result to the right by the fractional part
  result_if_frac_part_is_nonzero = builder.CreateShl(result_if_frac_part_is_nonzero, ref->valueInfo(oldf->getArg(0))->fixpType.scalarFracBitsAmt(), "result_if_frac_part_is_nonzero");

  // If fractional part is zero keep the original result
  result = builder.CreateSelect(fracPartIsZero, result, result_if_frac_part_is_nonzero, "result_final");

  LLVM_DEBUG(dbgs() << "Round logic created.\n");


  // Cast the integer to the return type
  if (arg_type->isFloatingPointTy() && ret_type->isFloatingPointTy()) {
    result = builder.CreateFPCast(result, ret_type);
  } else if (arg_type->isFloatingPointTy() && ret_type->isIntegerTy()) {
    result = builder.CreateFPToSI(result, ret_type);
  } else if (arg_type->isIntegerTy() && ret_type->isFloatingPointTy()) {
    result = builder.CreateSIToFP(result, ret_type);
  } else if (arg_type->isIntegerTy() && ret_type->isIntegerTy()) {
    result = builder.CreateIntCast(result, ret_type, true);
  }
  builder.CreateRet(result);


  return true;
}

// TODO: add an hashmap to dispatch
bool FloatToFixed::convertLibmFunction(
    Function *OldFunc, Function *NewFunc)
{
  assert(TaffoMath::isSupportedLibmFunction(OldFunc, Fixm));
  // TODO: demangle names
  // auto fName = demangle(OldFunc->getName().str());
  auto fName = OldFunc->getName().str();


  if (taffo::start_with(fName, "sin") || taffo::start_with(fName, "cos") ||
      taffo::start_with(fName, "_ZSt3cos") ||
      taffo::start_with(fName, "_ZSt3sin")) {
    return createSinCos(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "tan")) {
    return createTan(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "asin")) {
    return createASin(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "acos")) {
    return createACos(this, NewFunc, OldFunc);
  }

  // Exp, expm1 and exp2 are handled by the same function. Lazy evaluation should make us fall into the right case.
  if (taffo::start_with(fName, "expm1")) {
    return createExp(this, NewFunc, OldFunc, flttofix::ExpFunType::Expm1);
  }

  if (taffo::start_with(fName, "exp2")) {
    return createExp(this, NewFunc, OldFunc, flttofix::ExpFunType::Exp2);
  }

  if (taffo::start_with(fName, "atan")) {
    return createATan(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "exp")) {
    return createExp(this, NewFunc, OldFunc, flttofix::ExpFunType::Exp);
  }

  if (taffo::start_with(fName, "sqrt")) {
    return flttofix::createSqrt(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "hypot")) {
    return flttofix::createHypot(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "pow")) {
    return flttofix::createPow(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "cbrt")) {
    return flttofix::createCbrt(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "log10")) {
    return createLog10(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "log2")) {
    return createLog2(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "log1p")) {
    return createLog(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "log")) {
    return createLog(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "fma")) {
    return createFma(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "fma")) {
    return createFma(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "abs") || taffo::start_with(fName, "fabs")) {
    return createAbs(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "ceil")) {
    return createCeil(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "floor")) {
    return createFloor(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "trunc")) {
    return createTrunc(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "round")) {
    return createRound(this, NewFunc, OldFunc);
  }

  if (taffo::start_with(fName, "copysign")) {
    return createCopysign(this, NewFunc, OldFunc);
  }

  llvm_unreachable("Function not recognized");
}

} // namespace flttofix
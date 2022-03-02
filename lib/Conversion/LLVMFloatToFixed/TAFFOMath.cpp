#include "TAFFOMath.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/ErrorHandling.h"
#include <llvm/ADT/ArrayRef.h>
#include <llvm/Support/ErrorHandling.h>


namespace TaffoMath
{

/** Create a new fixedpoint from current float
 * MAY RETURN NULLPTR IF CONST IS NOT CREATED
 * @param cont context used to create instruction
 * @param float_to_fixed used to access private function
 * @param current_float float to be converted
 * @param match point used as match
 */
llvm::Constant *createFixedPointFromConst(
    llvm::LLVMContext &cont, FloatToFixed *float_to_fixed, double current_float,
    const FixedPointType &match)
{

  flttofix::FloatToFixed::TypeMatchPolicy typepol =
      flttofix::FloatToFixed::TypeMatchPolicy::ForceHint;
  APFloat val(current_float);

  APSInt fixval;
  FixedPointType outF;
  llvm::Constant *outI = nullptr;


  APFloat tmp(val);

  bool precise = false;
  tmp.convert(APFloatBase::IEEEdouble(), APFloat::rmTowardNegative, &precise);

  double dblval = tmp.convertToDouble();
  int nbits = match.scalarBitsAmt();
  mdutils::Range range(dblval, dblval);
  int minflt = float_to_fixed->isMaxIntPolicy(typepol) ? -1 : 0;
  mdutils::FPType t =
      taffo::fixedPointTypeFromRange(range, nullptr, nbits, minflt);
  outF = FixedPointType(&t);


  LLVM_DEBUG(dbgs() << "OutF: " << outF << " < Match:" << match << "\n");
  if (outF.scalarFracBitsAmt() < match.scalarFracBitsAmt()) {
    LLVM_DEBUG(dbgs() << "cannot insert " << current_float << " in " << match << "\n");
    return nullptr;
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
      return nullptr;
    }
  }

  Type *intty = outF.scalarToLLVMType(cont);
  outI = ConstantInt::get(intty, fixval);

  LLVM_DEBUG(dbgs() << "create int "
                    << (dyn_cast<llvm::Constant>(outI)->dump(), "") << "from "
                    << current_float << "\n");
  return outI;
}

Value *addAllocaToStart(FloatToFixed *ref, Function *oldf,
                        llvm::IRBuilder<> &builder, Type *to_alloca,
                        llvm::Value *ArraySize,
                        const llvm::Twine &Name)
{
  auto OldBB = builder.GetInsertBlock();
  LLVM_DEBUG(dbgs() << "Insert alloca inst\nOld basic block: " << OldBB << "\n");
  builder.SetInsertPoint(&(oldf->getEntryBlock()),
                         (oldf->getEntryBlock()).getFirstInsertionPt());
  Value *pointer_to_alloca = builder.CreateAlloca(to_alloca, ArraySize, Name);
  LLVM_DEBUG(dbgs() << "New Alloca: " << pointer_to_alloca << "\n");
  builder.SetInsertPoint(OldBB);
  return pointer_to_alloca;
}


// Overload to construct a global variable using its constructor's defaults.
Constant *getOrInsertGlobal(Module *M, StringRef Name, Type *Ty, unsigned addres_space)
{
  return M->getOrInsertGlobal(Name, Ty, [&] {
    return new GlobalVariable(*M, Ty, false, GlobalVariable::ExternalLinkage,
                              nullptr, Name, nullptr, llvm::GlobalValue::NotThreadLocal, addres_space);
  });
}


llvm::GlobalVariable *
createGlobalConst(llvm::Module *module, llvm::StringRef Name, llvm::Type *Ty,
                  Constant *initializer, llvm::MaybeAlign alignment)
{


  getOrInsertGlobal(module, Name, Ty, 1);
  auto global = module->getGlobalVariable(Name);
  global->setInitializer(initializer);
  global->setConstant(true);
  if (alignment->value() > 1) {
    global->setAlignment(alignment);
  }
  return global;
}

} // namespace TaffoMath

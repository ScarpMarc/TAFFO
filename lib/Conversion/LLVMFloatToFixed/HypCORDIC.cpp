/*
    Hyperbolic CORDIC for cosh, sinh, exp...
*/

#include "TAFFOMath.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include <string>
#include <vector>

#define DEBUG_TYPE "taffo-conversion"

bool createExp(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  //
  newfs->deleteBody();
  Value *generic;
  Module *M = oldf->getParent();

  // TODO: sinh cosh exp  

  // Retrieve context used in later instruction
  llvm::LLVMContext &cont(oldf->getContext());
  DataLayout dataLayout(M);
  LLVM_DEBUG(dbgs() << "\nGet Context " << &cont << "\n");
  // Get first basic block of function
  BasicBlock::Create(cont, "Entry", newfs);
  BasicBlock *where = &(newfs->getEntryBlock());
  LLVM_DEBUG(dbgs() << "\nGet entry point " << where);
  IRBuilder<> builder(where, where->getFirstInsertionPt());
  // Get return type fixed point
  flttofix::FixedPointType fxpret;
  flttofix::FixedPointType fxparg;
  bool foundRet = false;
  bool foundArg = false;
  TaffoMath::getFixedFromRet(ref, oldf, fxpret, foundRet);
  // get argument fixed point
  TaffoMath::getFixedFromArg(ref, oldf, fxparg, 0, foundArg);
  if (!foundRet || !foundArg) {
    return partialSpecialCall(newfs, foundRet, fxpret);
  }
  TaffoMath::pair_ftp_value<llvm::Value *> arg(fxparg);
  arg.value = newfs->arg_begin();
  auto truefxpret = fxpret;

  /*if ((fxpret.scalarBitsAmt() - fxpret.scalarFracBitsAmt()) < 5) {
    fxpret = flttofix::FixedPointType(true,
                                      fxpret.scalarBitsAmt() - 5,
                                      fxpret.scalarBitsAmt());
    LLVM_DEBUG(dbgs() << "New fxpret: " << fxpret << "\n");
  }*/

  LLVM_DEBUG(dbgs() << "fxpret: " << fxpret.scalarBitsAmt() << " frac part: " << fxpret.scalarFracBitsAmt() << " difference: " << fxpret.scalarBitsAmt() - fxpret.scalarFracBitsAmt() << "\n");

  auto int_type = fxpret.scalarToLLVMType(cont);
  
  // FIXME FIXME
  //auto internal_fxpt = flttofix::FixedPointType(true, fxpret.scalarBitsAmt() - 2, fxpret.scalarBitsAmt());
  /*
    In case the argument is positive we can use the same data type for x and y, as they will end up at a similar magnitude.

    In case the argument is negative, x and y will still end up at a similar magnitude, but with opposite signs.
    This means that we subtract one from the other and the return value will be close to 0 and we cannot rely on the estimated range for the output.

    The solution for now is to just use an intermediate fixed point type with a larger number of bits: we use 64 bits in total. We estimated that x and y may get up to about 20'000 for an exponent of -15; this means that they will fit into a data type with 16 bits in the integer part (i.e. 15 bits for the integer part and 1 bit for the sign).
  */
  auto internal_fxpt = flttofix::FixedPointType(true, 64-16, 64);

  // create local variable
  // TODO: Check bit width for this
  TaffoMath::pair_ftp_value<llvm::Value *> x_value(fxpret);
  TaffoMath::pair_ftp_value<llvm::Value *> y_value(fxpret);
  x_value.value = builder.CreateAlloca(int_type, nullptr, "x");
  y_value.value = builder.CreateAlloca(int_type, nullptr, "y");
  auto changeSign =
      builder.CreateAlloca(Type::getInt8Ty(cont), nullptr, "changeSign");
  auto changedFunction =
      builder.CreateAlloca(Type::getInt8Ty(cont), nullptr, "changefunc");
  auto specialAngle =
      builder.CreateAlloca(Type::getInt8Ty(cont), nullptr, "specialAngle");
  Value *arg_value = builder.CreateAlloca(int_type, nullptr, "arg");
  builder.CreateStore(newfs->getArg(0), arg_value);
  Value *i_iterator = builder.CreateAlloca(int_type, nullptr, "iterator");

  // create pi variable
  TaffoMath::pair_ftp_value<llvm::Constant *> pi(fxpret);
  TaffoMath::pair_ftp_value<llvm::Constant *> pi_2(fxpret);
  TaffoMath::pair_ftp_value<llvm::Constant *> pi_32(fxpret);
  TaffoMath::pair_ftp_value<llvm::Constant *> pi_half(fxpret);
  TaffoMath::pair_ftp_value<llvm::Constant *> pi_half_internal(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Constant *> kopp(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Constant *> zero(fxpret);
  TaffoMath::pair_ftp_value<llvm::Constant *> zeroarg(fxparg);
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_internal(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Constant *> one(fxpret);
  TaffoMath::pair_ftp_value<llvm::Constant *> one_internal(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Constant *> minus_one(fxpret);
  TaffoMath::pair_ftp_value<llvm::Constant *> minus_one_internal(internal_fxpt);
  bool pi_created = TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::pi, fxpret, pi.value, pi.fpt);
  bool pi_2_created = TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::pi_2, fxpret, pi_2.value, pi_2.fpt);
  bool pi_32_created = TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::pi_32, fxpret, pi_32.value, pi_32.fpt);
  bool pi_half_created = TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::pi_half, fxpret, pi_half.value,
      pi_half.fpt);
  bool done = TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::pi_half, internal_fxpt, pi_half_internal.value,
      pi_half_internal.fpt);

  bool kopp_created = TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::Kopp, internal_fxpt, kopp.value, kopp.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, fxpret, zero.value, zero.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, fxparg, zeroarg.value, zeroarg.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::one, fxpret, one.value, one.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::one, internal_fxpt, one_internal.value, one_internal.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, internal_fxpt, zero_internal.value, zero_internal.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::minus_one, fxpret, minus_one.value,
      minus_one.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::minus_one, internal_fxpt, minus_one_internal.value,
      minus_one_internal.fpt);
  std::string S_ret_point = "." + std::to_string(fxpret.scalarFracBitsAmt());


  if (pi_created)
    pi.value = TaffoMath::createGlobalConst(
        M, "pi" + S_ret_point, pi.fpt.scalarToLLVMType(cont), pi.value,
        dataLayout.getPrefTypeAlignment(pi.fpt.scalarToLLVMType(cont)));
  if (pi_2_created)
    pi_2.value = TaffoMath::createGlobalConst(
        M, "pi_2" + S_ret_point, pi_2.fpt.scalarToLLVMType(cont), pi_2.value,
        dataLayout.getPrefTypeAlignment(pi_2.fpt.scalarToLLVMType(cont)));
  if (pi_32_created)
    pi_32.value = TaffoMath::createGlobalConst(
        M, "pi_32" + S_ret_point,
        pi_32.fpt.scalarToLLVMType(cont), pi_32.value,
        dataLayout.getPrefTypeAlignment(pi_32.fpt.scalarToLLVMType(cont)));
  if (pi_half_created)
    pi_half.value = TaffoMath::createGlobalConst(
        M, "pi_half" + S_ret_point,
        pi_half.fpt.scalarToLLVMType(cont), pi_half.value,
        dataLayout.getPrefTypeAlignment(pi_half.fpt.scalarToLLVMType(cont)));
  pi_half_internal.value = TaffoMath::createGlobalConst(
      M,
      "pi_half_internal_" + std::to_string(internal_fxpt.scalarFracBitsAmt()),
      pi_half_internal.fpt.scalarToLLVMType(cont), pi_half_internal.value,
      dataLayout.getPrefTypeAlignment(
          pi_half_internal.fpt.scalarToLLVMType(cont)));
  if (kopp_created)
    kopp.value = TaffoMath::createGlobalConst(
        M, "kopp" + S_ret_point, kopp.fpt.scalarToLLVMType(cont), kopp.value,
        dataLayout.getPrefTypeAlignment(kopp.fpt.scalarToLLVMType(cont)));
  zero.value = TaffoMath::createGlobalConst(
      M, "zero" + S_ret_point, zero.fpt.scalarToLLVMType(cont), zero.value,
      dataLayout.getPrefTypeAlignment(zero.fpt.scalarToLLVMType(cont)));
  zeroarg.value = TaffoMath::createGlobalConst(
      M, "zero_arg" + S_ret_point, zeroarg.fpt.scalarToLLVMType(cont),
      zeroarg.value,
      dataLayout.getPrefTypeAlignment(zeroarg.fpt.scalarToLLVMType(cont)));
  one.value = TaffoMath::createGlobalConst(
      M, "one" + S_ret_point, one.fpt.scalarToLLVMType(cont), one.value,
      dataLayout.getPrefTypeAlignment(one.fpt.scalarToLLVMType(cont)));
  minus_one.value = TaffoMath::createGlobalConst(
      M, "minus_one" + S_ret_point, minus_one.fpt.scalarToLLVMType(cont),
      minus_one.value,
      dataLayout.getPrefTypeAlignment(minus_one.fpt.scalarToLLVMType(cont)));
  minus_one_internal.value = TaffoMath::createGlobalConst(
      M, "minus_one_internal." + std::to_string(internal_fxpt.scalarFracBitsAmt()), minus_one_internal.fpt.scalarToLLVMType(cont),
      minus_one_internal.value,
      dataLayout.getPrefTypeAlignment(minus_one.fpt.scalarToLLVMType(cont)));
  one_internal.value = TaffoMath::createGlobalConst(
      M, "one_internal." + std::to_string(internal_fxpt.scalarFracBitsAmt()), one_internal.fpt.scalarToLLVMType(cont),
      one_internal.value,
      dataLayout.getPrefTypeAlignment(minus_one.fpt.scalarToLLVMType(cont)));

  /** create arctan table
   **/
  LLVM_DEBUG(dbgs() << "Create arctan table"
                    << "\n");
  TaffoMath::pair_ftp_value<llvm::Constant *,
                            TaffoMath::TABLELENGHT>
      arctan_2power;
  llvm::AllocaInst *pointer_to_array = nullptr;
  if (!MathZFlag) {
    for (int i = 0; i < TaffoMath::TABLELENGHT; i++) {
      arctan_2power.fpt.push_back(flttofix::FixedPointType(fxpret));
      Constant *tmp = nullptr;
      auto &current_fpt = arctan_2power.fpt.front();
      TaffoMath::createFixedPointFromConst(
          cont, ref, TaffoMath::arctan_2power[i], internal_fxpt, tmp, current_fpt);
      arctan_2power.value.push_back(tmp);
      LLVM_DEBUG(dbgs() << i << ")");
    }


    auto arctanArrayType = llvm::ArrayType::get(arctan_2power.value[0]->getType(),
                                                TaffoMath::TABLELENGHT);

    LLVM_DEBUG(dbgs() << "ArrayType  " << arctanArrayType << "\n");
    auto arctanConstArray = llvm::ConstantArray::get(
        arctanArrayType, llvm::ArrayRef<llvm::Constant *>(arctan_2power.value));
    LLVM_DEBUG(dbgs() << "ConstantDataArray tmp2 " << arctanConstArray << "\n");
    auto alignement_arctan =
        dataLayout.getPrefTypeAlignment(arctan_2power.value[0]->getType());
    auto arctan_g =
        TaffoMath::createGlobalConst(M, "arctan_g." + std::to_string(internal_fxpt.scalarFracBitsAmt()), arctanArrayType,
                                     arctanConstArray, alignement_arctan);

    pointer_to_array = builder.CreateAlloca(arctanArrayType);
    pointer_to_array->setAlignment(llvm::Align(alignement_arctan));

    builder.CreateMemCpy(
        pointer_to_array, llvm::Align(alignement_arctan), arctan_g, llvm::Align(alignement_arctan),
        TaffoMath::TABLELENGHT * (int_type->getScalarSizeInBits() >> 3));
    LLVM_DEBUG(dbgs() << "\nAdd to newf arctan table"
                      << "\n");
  }

  // code gen
  auto int_8_zero = ConstantInt::get(Type::getInt8Ty(cont), 0);
  auto int_8_one = ConstantInt::get(Type::getInt8Ty(cont), 1);
  auto int_8_minus_one = ConstantInt::get(Type::getInt8Ty(cont), -1);
  builder.CreateStore(int_8_zero, changeSign);
  builder.CreateStore(int_8_zero, changedFunction);
  builder.CreateStore(int_8_zero, specialAngle);
  BasicBlock *body = BasicBlock::Create(cont, "body", newfs);
  builder.CreateBr(body);
  builder.SetInsertPoint(body);
  arg.value = arg_value;
  BasicBlock *return_point = BasicBlock::Create(cont, "return_point", newfs);
  // handle unsigned arg
  if (!fxparg.scalarIsSigned()) {
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), ConstantInt::get(int_type, 1)), arg_value);
    fxparg.scalarFracBitsAmt() = fxparg.scalarFracBitsAmt() - 1;
    fxparg.scalarIsSigned() = true;
  }


  // handle negative
  if (isSin) {
    // sin(-x) == -sin(x)
    {
      BasicBlock *true_greater_zero =
          BasicBlock::Create(cont, "true_greater_zero", newfs);
      BasicBlock *false_greater_zero = BasicBlock::Create(cont, "body", newfs);

      generic = builder.CreateICmpSLT(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value, "arg"),
                                      builder.CreateLoad(getElementTypeFromValuePointer(zeroarg.value), zeroarg.value));
      generic =
          builder.CreateCondBr(generic, true_greater_zero, false_greater_zero);
      builder.SetInsertPoint(true_greater_zero);
      generic = builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(zeroarg.value), zeroarg.value),
                                  builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value));
      builder.CreateStore(
          builder.CreateXor(builder.CreateLoad(getElementTypeFromValuePointer(changeSign), changeSign), int_8_minus_one),
          changeSign);
      builder.CreateStore(generic, arg_value);
      builder.CreateBr(false_greater_zero);
      builder.SetInsertPoint(false_greater_zero);
    }

  } else {
    // cos(-x) == cos(x)
    {
      BasicBlock *true_greater_zero =
          BasicBlock::Create(cont, "true_greater_zero", newfs);
      BasicBlock *false_greater_zero = BasicBlock::Create(cont, "body", newfs);

      generic = builder.CreateICmpSLT(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value, "arg"),
                                      builder.CreateLoad(getElementTypeFromValuePointer(zeroarg.value), zeroarg.value));
      generic =
          builder.CreateCondBr(generic, true_greater_zero, false_greater_zero);
      builder.SetInsertPoint(true_greater_zero);
      generic = builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(zeroarg.value), zeroarg.value),
                                  builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value));
      builder.CreateStore(generic, arg_value);
      builder.CreateBr(false_greater_zero);
      builder.SetInsertPoint(false_greater_zero);
    }
  }

  fixrangeSinCos(ref, newfs, fxparg, fxpret, arg_value, builder);

  // special case
  {
    // x = pi/2

    if (pi_half_created) {
      BasicBlock *BTrue = BasicBlock::Create(cont, "equal_pi_2", newfs);
      BasicBlock *BFalse = BasicBlock::Create(cont, "body", newfs);
      generic = builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value, "arg"),
                                     builder.CreateLoad(getElementTypeFromValuePointer(pi_half.value), pi_half.value));
      builder.CreateCondBr(generic, BTrue, BFalse);
      builder.SetInsertPoint(BTrue);
      builder.CreateStore(int_8_one, specialAngle);
      builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(one_internal.value), one_internal.value), y_value.value);
      builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(zero.value), zero.value), x_value.value);
      builder.CreateBr(BFalse);
      builder.SetInsertPoint(BFalse);
    }
    // x= pi
    if (pi_created) {
      BasicBlock *BTrue = BasicBlock::Create(cont, "equal_pi", newfs);
      BasicBlock *BFalse = BasicBlock::Create(cont, "body", newfs);
      generic = builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value, "arg"),
                                     builder.CreateLoad(getElementTypeFromValuePointer(pi.value), pi.value));
      builder.CreateCondBr(generic, BTrue, BFalse);
      builder.SetInsertPoint(BTrue);
      builder.CreateStore(int_8_one, specialAngle);
      builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(zero.value), zero.value), y_value.value);
      builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(minus_one_internal.value), minus_one_internal.value), x_value.value);
      builder.CreateBr(BFalse);
      builder.SetInsertPoint(BFalse);
    }
    // x = pi_32
    if (pi_32_created) {
      BasicBlock *BTrue = BasicBlock::Create(cont, "equal_pi_32", newfs);
      BasicBlock *BFalse = BasicBlock::Create(cont, "body", newfs);
      generic = builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value, "arg"),
                                     builder.CreateLoad(getElementTypeFromValuePointer(pi_32.value), pi_32.value));
      builder.CreateCondBr(generic, BTrue, BFalse);
      builder.SetInsertPoint(BTrue);
      builder.CreateStore(int_8_one, specialAngle);
      builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(minus_one_internal.value), minus_one_internal.value), y_value.value);
      builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(zero.value), zero.value), x_value.value);
      builder.CreateBr(BFalse);
      builder.SetInsertPoint(BFalse);
    }
    // x = 0

    {
      BasicBlock *BTrue = BasicBlock::Create(cont, "equal_0", newfs);
      BasicBlock *BFalse = BasicBlock::Create(cont, "body", newfs);
      generic = builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value, "arg"),
                                     builder.CreateLoad(getElementTypeFromValuePointer(zero.value), zero.value));
      builder.CreateCondBr(generic, BTrue, BFalse);
      builder.SetInsertPoint(BTrue);
      builder.CreateStore(int_8_one, specialAngle);
      builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(zero.value), zero.value), y_value.value);
      builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(one_internal.value), one_internal.value), x_value.value);
      builder.CreateBr(BFalse);
      builder.SetInsertPoint(BFalse);
    }
    // handle premature return
    {
      BasicBlock *BTrue = BasicBlock::Create(cont, "Special", newfs);
      BasicBlock *BFalse = BasicBlock::Create(cont, "body", newfs);
      generic = builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(specialAngle), specialAngle, "arg"),
                                     int_8_one);
      builder.CreateCondBr(generic, BTrue, BFalse);
      builder.SetInsertPoint(BTrue);
      builder.CreateBr(return_point);
      builder.SetInsertPoint(BFalse);
    }
  }

  if (isSin) {
    // angle > pi_half && angle < pi sin(x) = cos(x - pi_half)
    if (pi_half_created && pi_created) {
      BasicBlock *in_II_quad = BasicBlock::Create(cont, "in_II_quad", newfs);
      BasicBlock *not_in_II_quad = BasicBlock::Create(cont, "body", newfs);
      generic = builder.CreateICmpSLT(
          builder.CreateLoad(getElementTypeFromValuePointer(pi_half.value), pi_half.value, "pi_half"),
          builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), "arg_greater_pi_half");
      Value *generic2 = builder.CreateICmpSLT(
          builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), builder.CreateLoad(getElementTypeFromValuePointer(pi.value), pi.value, "pi"),
          "arg_less_pi");
      generic = builder.CreateAnd(generic, generic2);
      builder.CreateCondBr(generic, in_II_quad, not_in_II_quad);
      builder.SetInsertPoint(in_II_quad);
      builder.CreateStore(builder.CreateXor(builder.CreateLoad(getElementTypeFromValuePointer(changedFunction), changedFunction),
                                            int_8_minus_one),
                          changedFunction);
      builder.CreateStore(builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value),
                                            builder.CreateLoad(getElementTypeFromValuePointer(pi_half.value), pi_half.value)),
                          arg_value);
      builder.CreateBr(not_in_II_quad);
      builder.SetInsertPoint(not_in_II_quad);
    }
    // angle > pi&& angle < pi_32(x) sin(x) = -sin(x - pi)
    if (pi_32_created && pi_created) {
      BasicBlock *in_III_quad = BasicBlock::Create(cont, "in_III_quad", newfs);
      BasicBlock *not_in_III_quad = BasicBlock::Create(cont, "body", newfs);
      generic = builder.CreateICmpSLT(builder.CreateLoad(getElementTypeFromValuePointer(pi.value), pi.value, "pi"),
                                      builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value),
                                      "arg_greater_pi");
      Value *generic2 = builder.CreateICmpSLT(
          builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value),
          builder.CreateLoad(getElementTypeFromValuePointer(pi_32.value), pi_32.value, "pi_32"), "arg_less_pi_32");
      generic = builder.CreateAnd(generic, generic2);
      builder.CreateCondBr(generic, in_III_quad, not_in_III_quad);
      builder.SetInsertPoint(in_III_quad);
      builder.CreateStore(
          builder.CreateXor(builder.CreateLoad(getElementTypeFromValuePointer(changeSign), changeSign), int_8_minus_one),
          changeSign);
      builder.CreateStore(builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value),
                                            builder.CreateLoad(getElementTypeFromValuePointer(pi.value), pi.value)),
                          arg_value);
      builder.CreateBr(not_in_III_quad);
      builder.SetInsertPoint(not_in_III_quad);
    }
    // angle > pi_32&& angle < pi_2(x) sin(x) = -cos(x - pi_32);
    if (pi_32_created && pi_2_created) {
      BasicBlock *in_IV_quad = BasicBlock::Create(cont, "in_IV_quad", newfs);
      BasicBlock *not_in_IV_quad = BasicBlock::Create(cont, "body", newfs);
      generic = builder.CreateICmpSLT(builder.CreateLoad(getElementTypeFromValuePointer(pi_32.value), pi_32.value, "pi_32"),
                                      builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value),
                                      "arg_greater_pi_32");
      Value *generic2 = builder.CreateICmpSLT(
          builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), builder.CreateLoad(getElementTypeFromValuePointer(pi_2.value), pi_2.value, "pi_2"),
          "arg_less_2pi");
      generic = builder.CreateAnd(generic, generic2);
      builder.CreateCondBr(generic, in_IV_quad, not_in_IV_quad);
      builder.SetInsertPoint(in_IV_quad);
      builder.CreateStore(
          builder.CreateXor(builder.CreateLoad(getElementTypeFromValuePointer(changeSign), changeSign), int_8_minus_one),
          changeSign);
      builder.CreateStore(builder.CreateXor(builder.CreateLoad(getElementTypeFromValuePointer(changedFunction), changedFunction),
                                            int_8_minus_one),
                          changedFunction);
      builder.CreateStore(builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value),
                                            builder.CreateLoad(getElementTypeFromValuePointer(pi_32.value), pi_32.value)),
                          arg_value);
      builder.CreateBr(not_in_IV_quad);
      builder.SetInsertPoint(not_in_IV_quad);
    }
  } else {

    // angle > pi_half && angle < pi cos(x) = -sin(x - pi_half);
    if (pi_half_created && pi_created) {
      BasicBlock *in_II_quad = BasicBlock::Create(cont, "in_II_quad", newfs);
      BasicBlock *not_in_II_quad = BasicBlock::Create(cont, "body", newfs);
      generic = builder.CreateICmpSLT(
          builder.CreateLoad(getElementTypeFromValuePointer(pi_half.value), pi_half.value, "pi_half"),
          builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), "arg_greater_pi_half");
      Value *generic2 = builder.CreateICmpSLT(
          builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), builder.CreateLoad(getElementTypeFromValuePointer(pi.value), pi.value, "pi"),
          "arg_less_pi");
      generic = builder.CreateAnd(generic, generic2);
      builder.CreateCondBr(generic, in_II_quad, not_in_II_quad);
      builder.SetInsertPoint(in_II_quad);
      builder.CreateStore(
          builder.CreateXor(builder.CreateLoad(getElementTypeFromValuePointer(changeSign), changeSign), int_8_minus_one),
          changeSign);
      builder.CreateStore(builder.CreateXor(builder.CreateLoad(getElementTypeFromValuePointer(changedFunction), changedFunction),
                                            int_8_minus_one),
                          changedFunction);
      builder.CreateStore(builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value),
                                            builder.CreateLoad(getElementTypeFromValuePointer(pi_half.value), pi_half.value)),
                          arg_value);
      builder.CreateBr(not_in_II_quad);
      builder.SetInsertPoint(not_in_II_quad);
    }
    // angle > pi&& angle < pi_32(x) cos(x) = -cos(x-pi)
    if (pi_32_created && pi_created) {
      BasicBlock *in_III_quad = BasicBlock::Create(cont, "in_III_quad", newfs);
      BasicBlock *not_in_III_quad = BasicBlock::Create(cont, "body", newfs);
      generic = builder.CreateICmpSLT(builder.CreateLoad(getElementTypeFromValuePointer(pi.value), pi.value, "pi"),
                                      builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value),
                                      "arg_greater_pi");
      Value *generic2 = builder.CreateICmpSLT(
          builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value),
          builder.CreateLoad(getElementTypeFromValuePointer(pi_32.value), pi_32.value, "pi_32"), "arg_less_pi_32");
      generic = builder.CreateAnd(generic, generic2);
      builder.CreateCondBr(generic, in_III_quad, not_in_III_quad);
      builder.SetInsertPoint(in_III_quad);
      builder.CreateStore(
          builder.CreateXor(builder.CreateLoad(getElementTypeFromValuePointer(changeSign), changeSign), int_8_minus_one),
          changeSign);
      builder.CreateStore(builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value),
                                            builder.CreateLoad(getElementTypeFromValuePointer(pi.value), pi.value)),
                          arg_value);
      builder.CreateBr(not_in_III_quad);
      builder.SetInsertPoint(not_in_III_quad);
    }
    // angle > pi_32&& angle < pi_2(x) cos(x) = sin(angle - pi_32);
    if (pi_32_created && pi_2_created) {
      BasicBlock *in_IV_quad = BasicBlock::Create(cont, "in_IV_quad", newfs);
      BasicBlock *not_in_IV_quad = BasicBlock::Create(cont, "body", newfs);
      generic = builder.CreateICmpSLT(builder.CreateLoad(getElementTypeFromValuePointer(pi_32.value), pi_32.value, "pi_32"),
                                      builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value),
                                      "arg_greater_pi_32");
      Value *generic2 = builder.CreateICmpSLT(
          builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), builder.CreateLoad(getElementTypeFromValuePointer(pi_2.value), pi_2.value, "pi_2"),
          "arg_less_2pi");
      generic = builder.CreateAnd(generic, generic2);
      builder.CreateCondBr(generic, in_IV_quad, not_in_IV_quad);
      builder.SetInsertPoint(in_IV_quad);
      builder.CreateStore(builder.CreateXor(builder.CreateLoad(getElementTypeFromValuePointer(changedFunction), changedFunction),
                                            int_8_minus_one),
                          changedFunction);
      builder.CreateStore(builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value),
                                            builder.CreateLoad(getElementTypeFromValuePointer(pi_32.value), pi_32.value)),
                          arg_value);
      builder.CreateBr(not_in_IV_quad);
      builder.SetInsertPoint(not_in_IV_quad);
    }
  }


  // calculate sin and cos
  if (!MathZFlag) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), internal_fxpt.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), arg_value);

    auto zero_arg = builder.CreateLoad(getElementTypeFromValuePointer(zero.value), zero.value);
    // TODO: Add constant
    // Initialise x and y to the initial constant (which depends on the amount of iterations we do)
    // x=An
    builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(const_An.value), const_An.value), x_value.value);
    // y=An
    builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(const_An.value), const_An.value), y_value.value);

    // Blocks where we check loop boundaries
    BasicBlock *check_loop_negatives = BasicBlock::Create(cont, "check_loop_negatives", newfs);
    BasicBlock *check_loop_positives = BasicBlock::Create(cont, "check_loop_positives", newfs);

    // Main loop bodies
    BasicBlock *start_loop_negatives = BasicBlock::Create(cont, "start_loop_negatives", newfs);
    BasicBlock *start_loop_positives = BasicBlock::Create(cont, "start_loop_positives", newfs);
    BasicBlock *epilog_loop = BasicBlock::Create(cont, "epilog_loop", newfs);

    /*
      We need to iterate from -m to 0 and then from 1 to n.

      We first loop on the negative values, then we loop on the positive values.
      The table is the same.
    */

    // NEGATIVE LOOP

    builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(zero.value), zero.value), i_iterator);

    builder.CreateBr(check_loop_negatives);
    builder.SetInsertPoint(check_loop_negatives);

    // Check whether i < m; if so, go to loop body. Else, go to positive loop.
    Value *iIsLessThanM = builder.CreateICmpSLT(
        builder.CreateLoad(getElementTypeFromValuePointer(i_iterator), i_iterator),
        ConstantInt::get(int_type, TaffoMath::cordic_exp_negative_iterations));

    // Execute the loop if i < m; else, go to the positive loop.
    builder.CreateCondBr(iIsLessThanM, start_loop_negatives,
                         check_loop_positives);
    {    
      builder.SetInsertPoint(start_loop_negatives);

      // sign = arg >= 0 ? 1 : -1;
      Value *update_sign = builder.CreateSelect(
        builder.CreateICmpSGE(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), zero_arg),
        ConstantInt::get(int_type, 1), ConstantInt::get(int_type, -1));

      // update_sign > 0 ?
      auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_arg);

      // shift_amt = i+2
      Value *shift_amt = builder.CreateAdd(
          builder.CreateLoad(getElementTypeFromValuePointer(i_iterator), i_iterator),
          ConstantInt::get(int_type, 2));

      // Temp value to store y_{k+1}
      Value *x_update;
      Value *y_update;

      { 
        // Update y. The update reads x.

        // Calculate x * (2 ^ -shift_amt)
        Value *y_update = builder.CreateAShr(
            builder.CreateLoad(getElementTypeFromValuePointer(x_value.value), x_value.value), shift_amt);

        // Calculate x - x * (2 ^ -shift_amt)
        y_update = builder.CreateSub(
            builder.CreateLoad(getElementTypeFromValuePointer(x_value.value), x_value.value), y_update);   

        // Calculate (update_sign > 0 ? -(x - x * (2 ^ -shift_amt)) : (x - x * (2 ^ -shift_amt)));
        y_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg, y_update), y_update);

        // y_{k+1} = y_k + y_update. Set to temp value since we will need to use y next.
        y_update = builder.CreateAdd(
            builder.CreateLoad(getElementTypeFromValuePointer(y_value.value), y_value.value), y_update);
      }

      {
        // Update x. The update reads y.

        // Calculate y * (2 ^ -shift_amt)
        x_update = builder.CreateAShr(
            builder.CreateLoad(getElementTypeFromValuePointer(y_value.value), y_value.value), shift_amt);

        // Calculate y - y * (2 ^ -shift_amt)
        x_update = builder.CreateSub(
            builder.CreateLoad(getElementTypeFromValuePointer(y_value.value), y_value.value), x_update);   

        // Calculate (update_sign > 0 ? -(y - y * (2 ^ -shift_amt)) : (y - y * (2 ^ -shift_amt)));
        x_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg, x_update), x_update);

        // x_{k+1} = x_k + x_update
        x_update =
          builder.CreateAdd(x_update, builder.CreateLoad(getElementTypeFromValuePointer(x_value.value), x_value.value));
      }

      // Store y_update into y
      builder.CreateStore(y_update, y_value.value);

      // Store x_update into x
      builder.CreateStore(x_update, x_value.value);

      {
        // Update z (= arg)

        // Calculate arctanh_2power[i]
        Value *update_z = builder.CreateGEP(getElementTypeFromValuePointer(pointer_to_arctanh_array), pointer_to_arctanh_array,
                                {zero_arg, builder.CreateLoad(getElementTypeFromValuePointer(i_iterator), i_iterator)});

        update_z = builder.CreateLoad(getElementTypeFromValuePointer(update_z), update_z);
        
        update_z = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg, update_z), update_z);

        builder.CreateStore(
          builder.CreateAdd(update_z, builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value)), arg_value);
      }
        
      // i++
      builder.CreateStore(builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(i_iterator), i_iterator),
                                          ConstantInt::get(int_type, 1)),
                        i_iterator);
      builder.CreateBr(check_loop_negatives);
    }

    // POSITIVE LOOP

    builder.CreateBr(check_loop_positives);
    builder.SetInsertPoint(check_loop_positives);

    // Check whether i < (m+n); if so, go to loop body. Else, go to positive loop.
    Value *iIsLessThanN = builder.CreateICmpSLT(
      builder.CreateLoad(getElementTypeFromValuePointer(i_iterator), i_iterator),
      ConstantInt::get(int_type, TaffoMath::cordic_exp_total_iterations));

    // Execute the loop if i < m+n; else, go to the end of the function.
    builder.CreateCondBr(iIsLessThanN, start_loop_positives,
                        return_point);
    {
      builder.SetInsertPoint(start_loop_positives);

      // sign = arg >= 0 ? 1 : -1;
      Value *update_sign = builder.CreateSelect(
        builder.CreateICmpSGE(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), zero_arg),
        ConstantInt::get(int_type, 1), ConstantInt::get(int_type, -1));

      // update_sign > 0 ?
      auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_arg);

      // shift_amt = i-m since we do not reset i
      Value *shift_amt =  builder.CreateSub(
          builder.CreateLoad(getElementTypeFromValuePointer(i_iterator), i_iterator),
          ConstantInt::get(int_type, TaffoMath::cordic_exp_negative_iterations));

      // Temp value to store y_{k+1}
      Value *x_update;
      Value *y_update;

      { 
        // Update y. The update reads x.

        // Calculate x * (2 ^ -shift_amt)
        Value *y_update = builder.CreateAShr(
            builder.CreateLoad(getElementTypeFromValuePointer(x_value.value), x_value.value), shift_amt);

        // Calculate (update_sign > 0 ? -(x - x * (2 ^ -shift_amt)) : (x - x * (2 ^ -shift_amt)));
        y_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg, y_update), y_update);

        // y_{k+1} = y_k + y_update. Set to temp value since we will need to use y next.
        y_update = builder.CreateAdd(
            builder.CreateLoad(getElementTypeFromValuePointer(y_value.value), y_value.value), y_update);
      }

      {
        // Update x. The update reads y.

        // Calculate y * (2 ^ -shift_amt)
        x_update = builder.CreateAShr(
            builder.CreateLoad(getElementTypeFromValuePointer(y_value.value), y_value.value), shift_amt);

        // Calculate (update_sign > 0 ? -(y - y * (2 ^ -shift_amt)) : (y - y * (2 ^ -shift_amt)));
        x_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg, x_update), x_update);

        // x_{k+1} = x_k + x_update
        x_update =
          builder.CreateAdd(x_update, builder.CreateLoad(getElementTypeFromValuePointer(x_value.value), x_value.value));
      }

      // Store y_update into y
      builder.CreateStore(y_update, y_value.value);

      // Store x_update into x
      builder.CreateStore(x_update, x_value.value);

      {
        // Update z (= arg)

        // Calculate arctanh_2power[i]
        Value *update_z = builder.CreateGEP(getElementTypeFromValuePointer(pointer_to_arctanh_array), pointer_to_arctanh_array,
                                {zero_arg, builder.CreateLoad(getElementTypeFromValuePointer(i_iterator), i_iterator)});

        update_z = builder.CreateLoad(getElementTypeFromValuePointer(update_z), update_z);
        
        update_z = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg, update_z), update_z);

        builder.CreateStore(
          builder.CreateAdd(update_z, builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value)), arg_value);
      }
        
      // i++
      builder.CreateStore(builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(i_iterator), i_iterator),
                                          ConstantInt::get(int_type, 1)),
                        i_iterator);
      builder.CreateBr(check_loop_negatives);

      // Set the insert point to the end of the function, which is after the else.
      builder.SetInsertPoint(return_point);
    }
  } else {
    // TODO
  }    

  {
    // TODO: handle other functions
  }

  if (internal_fxpt.scalarFracBitsAmt() > truefxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), internal_fxpt.scalarFracBitsAmt() - truefxpret.scalarFracBitsAmt()), arg_value);
  } else if (internal_fxpt.scalarFracBitsAmt() < truefxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), truefxpret.scalarFracBitsAmt() - internal_fxpt.scalarFracBitsAmt()), arg_value);
  }

  auto ret = builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value);

  BasicBlock *end = BasicBlock::Create(cont, "end", newfs);
  builder.CreateBr(end);
  builder.SetInsertPoint(end);
  builder.CreateRet(ret);
  return true;
}
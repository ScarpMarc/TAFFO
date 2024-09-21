/*
    Hyperbolic CORDIC for cosh, sinh, exp...
*/

#include "HypCORDIC.h"
#include "TAFFOMath.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include <string>
#include <vector>

#define DEBUG_TYPE "taffo-conversion"

namespace flttofix
{

bool createExp2(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  //
  newfs->deleteBody();

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
    LLVM_DEBUG(dbgs() << "Return or argument not found\n");
    return partialSpecialCall(newfs, foundRet, fxpret);
  }

  LLVM_DEBUG(dbgs() << "fxpret: " << fxpret.scalarBitsAmt() << " frac part: " << fxpret.scalarFracBitsAmt() << " difference: " << fxpret.scalarBitsAmt() - fxpret.scalarFracBitsAmt() << "\n");

  auto int_type = fxpret.scalarToLLVMType(cont);
  LLVM_DEBUG(dbgs() << "Return fixed point type: ");
  int_type->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // Generate strings for constants names
  std::string S_arg_point = "." + std::to_string(fxparg.scalarFracBitsAmt());
  std::string S_ret_point = "." + std::to_string(fxpret.scalarFracBitsAmt());

  // ----------------------------------------------------

  // The pointer to the value that is actually returned.
  Value *return_value_ptr = builder.CreateAlloca(int_type, nullptr, "return_value_ptr");

  // Pointer to the argument
  Value *arg_ptr = builder.CreateAlloca(int_type, nullptr, "arg");
  builder.CreateStore(newfs->getArg(0), arg_ptr);

  LLVM_DEBUG(dbgs() << "arg_ptr: ");
  arg_ptr->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  /*
    The return type should hold at least 1 bit of integer part.
    */

  auto truefxpret = fxpret;
  if (fxpret.scalarIntegerBitsAmt() < 1) {
    LLVM_DEBUG(dbgs() << "Return type is too small: shifting argument to the right by " << 1 - fxparg.scalarIntegerBitsAmt() << " bit(s)\n");
    builder.CreateStore(builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), ConstantInt::get(int_type, 1 - fxparg.scalarIntegerBitsAmt()), "arg_shifted_was_too_small"), arg_ptr);
    fxparg.scalarFracBitsAmt() = fxparg.scalarBitsAmt() - 1;
    LLVM_DEBUG(dbgs() << "New argument fixed point type: " << fxparg << "\n");
  }

  // ----------------------------------------------------
  // Some variables we will need to handle special cases.
  // More variables will be declared later.

  // Pointer to one (for returning)
  TaffoMath::pair_ftp_value<llvm::Constant *> one_ptr_ret(fxparg);
  bool one_ptr_ret_created = TaffoMath::createFixedPointFromConst(
      cont, ref, 1.0, fxparg, one_ptr_ret.value, one_ptr_ret.fpt);
  if (one_ptr_ret_created) {
    one_ptr_ret.value = TaffoMath::createGlobalConst(
        M, "one_ptr_arg" + S_arg_point, one_ptr_ret.fpt.scalarToLLVMType(cont), one_ptr_ret.value,
        dataLayout.getPrefTypeAlignment(one_ptr_ret.fpt.scalarToLLVMType(cont)));
  } else {
    LLVM_DEBUG(dbgs() << "ERROR: Could not create the constant 1.0\n");
    llvm_unreachable("Could not create the constant 1.0. Exp2 cannot continue.");
    return false;
  }

  LLVM_DEBUG(dbgs() << "Created special constant\n");

  // ----------------------------------------------------
  // Basic blocks

  // Block for the initialization of the loop
  BasicBlock *init = BasicBlock::Create(cont, "init", newfs);

  // Blocks where we check loop boundaries
  BasicBlock *check_arg_sign = BasicBlock::Create(cont, "check_arg_sign", newfs);

  BasicBlock *handle_positive_arg = BasicBlock::Create(cont, "handle_positive_arg", newfs);
  BasicBlock *handle_negative_arg = BasicBlock::Create(cont, "handle_negative_arg", newfs);

  // Main loop bodies
  BasicBlock *handle_integer_part = BasicBlock::Create(cont, "handle_integer_part", newfs);
  BasicBlock *handle_fractional_part = BasicBlock::Create(cont, "handle_fractional_part", newfs);
  BasicBlock *fractional_part_loop_body = BasicBlock::Create(cont, "fractional_part_loop_body", newfs);

  // In case we did not need to return a special value, we will cast the result to the return type here
  BasicBlock *finalize = BasicBlock::Create(cont, "finalize", newfs);

  // End block, which returns the result
  BasicBlock *end = BasicBlock::Create(cont, "end", newfs);

  // Blocks for special cases
  /*
  The "pre" blocks are used to avoid non-terminated blocks: before each special case, we test
    whether the TAFFO variables it needs were created. If they were not, we (at TAFFO compile time)
    avoid placing the block directly and immediately jump to the next special case.
    The problem is that in case we DO place the special case, the next one will have an additional unconditional
    branch instruction upon entry, which is illegal in LLVM since there already was a conditional branch that tested the special
    case (at TAFFO's runtime, compiling the target program).

    The solution is to use a "pre" block which we always place: in case we do create the special case, we jump to the "pre" block,
    which then jumps to the special case. In case we do not create the special case, we jump to the next special case directly.
    */

  BasicBlock *checkArgIsZero = BasicBlock::Create(cont, "check_arg_is_zero", newfs);
  BasicBlock *argIsZero = BasicBlock::Create(cont, "arg_is_zero", newfs);

  BasicBlock *init_pre = BasicBlock::Create(cont, "init_pre", newfs);

  // ----------------------------------------------------
  // Special cases: if we fall into one of these, we can return our special value directly
  // and skip the rest of the function.

  /*
Check whether we successfully created the constant; if not, we calculate the result at runtime.
From an IR perspective, we immediately jump to the next special case.
*/
  LLVM_DEBUG(dbgs() << "Create checkArgIsZero"
                    << "\n");

  builder.CreateBr(checkArgIsZero);
  builder.SetInsertPoint(checkArgIsZero);
  {
    // Arg = 0 -> return 1

    Value *check = builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_initial"),
                                        ConstantInt::get(int_type, 0), "arg_is_zero");

    builder.CreateCondBr(check, argIsZero, init_pre);

    builder.SetInsertPoint(argIsZero);
    {
      // Copy the result to the return value
      builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(one_ptr_ret.value), one_ptr_ret.value), return_value_ptr);
      builder.CreateBr(end);
    }
  }


  builder.SetInsertPoint(init_pre);

  LLVM_DEBUG(dbgs() << "Create init"
                    << "\n");
  builder.CreateBr(init);
  builder.SetInsertPoint(init);

  // ----------------------------------------------------
  // Create the table for the Taylor series

  TaffoMath::pair_ftp_value<llvm::Constant *,
                            TaffoMath::TABLELENGHT>
      Taylor_table;

  LLVM_DEBUG(dbgs() << "===== Create Taylor series table ====="
                    << "\n");

  llvm::AllocaInst *pointer_to_Taylor_array = nullptr;

  for (int i = 0; i < TaffoMath::TABLELENGHT; i++) {
    LLVM_DEBUG(dbgs() << "Element " << i << ":\n");
    Taylor_table.fpt.push_back(flttofix::FixedPointType(fxpret));
    Constant *tmp = nullptr;
    auto &current_fpt = Taylor_table.fpt.front();
    bool this_value_created = TaffoMath::createFixedPointFromConst(
        cont, ref, flttofix::exp2_table[i], fxpret, tmp, current_fpt);

    if (!this_value_created) {
      LLVM_DEBUG(dbgs() << "===== ERROR: Could not create the " << i << "th element of the Taylor series table\n");
      std::string err_msg = "Could not create one the " + std::to_string(i) + "th element of the Taylor series table. Exp2 cannot continue.";
      llvm_unreachable(err_msg.c_str());
      return false;
    }

    Taylor_table.value.push_back(tmp);
    LLVM_DEBUG(dbgs() << "\n");
  }

  auto TaylorArrayType = llvm::ArrayType::get(Taylor_table.value[0]->getType(),
                                              TaffoMath::TABLELENGHT);
  LLVM_DEBUG(dbgs() << "TaylorArrayType: ");
  TaylorArrayType->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  auto TaylorConstArray = llvm::ConstantArray::get(
      TaylorArrayType, llvm::ArrayRef<llvm::Constant *>(Taylor_table.value));

  LLVM_DEBUG(dbgs() << "TaylorConstArray: ");
  TaylorArrayType->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  auto alignement_Taylor =
      dataLayout.getPrefTypeAlignment(Taylor_table.value[0]->getType());
  auto Taylor_g =
      TaffoMath::createGlobalConst(M, "Taylor_g." + std::to_string(fxpret.scalarFracBitsAmt()), TaylorArrayType,
                                   TaylorConstArray, alignement_Taylor);

  pointer_to_Taylor_array = builder.CreateAlloca(TaylorArrayType, nullptr, "Taylor_array");
  pointer_to_Taylor_array->setAlignment(llvm::Align(alignement_Taylor));

  builder.CreateMemCpy(
      pointer_to_Taylor_array, llvm::Align(alignement_Taylor), Taylor_g, llvm::Align(alignement_Taylor),
      TaffoMath::TABLELENGHT * (int_type->getScalarSizeInBits() >> 3));
  LLVM_DEBUG(dbgs() << "\nAdd to newf arctanh table. Copied " << TaffoMath::TABLELENGHT * (int_type->getScalarSizeInBits() >> 3) << " bytes\n");

  LLVM_DEBUG(dbgs() << "fxparg: " << fxparg.scalarBitsAmt() << " frac part: " << fxparg.scalarFracBitsAmt() << " difference: " << fxparg.scalarBitsAmt() - fxparg.scalarFracBitsAmt() << "\n");

  // calculate exp2

  LLVM_DEBUG(dbgs() << "Starting exp2 routine"
                    << "\n");

  // Iterator for the fractional part loop
  Value *i_ptr = builder.CreateAlloca(int_type, nullptr, "i_ptr");
  builder.CreateStore(ConstantInt::get(int_type, 0), i_ptr);

  Value *arg_is_positive_ptr = builder.CreateAlloca(int_type, nullptr, "arg_is_positive_ptr");

  Value *arg_value = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg");

  Value *integer_part = builder.CreateAShr(arg_value, fxparg.scalarFracBitsAmt(), "integer_part");
  Value *fractional_part = builder.CreateAnd(arg_value, ConstantInt::get(int_type, (1 << fxparg.scalarFracBitsAmt()) - 1), "fractional_part");

  // If the argument is unsigned, we branch to the integer handling block directly
  if (!fxparg.scalarIsSigned()) {
    builder.CreateStore(ConstantInt::get(int_type, 1), arg_is_positive_ptr);

    builder.CreateBr(handle_integer_part);
  } else
    builder.CreateBr(check_arg_sign);

  // ----------------------------------------------------
  // Check whether the argument is positive or negative

  builder.SetInsertPoint(check_arg_sign);
  {
    Value *check = builder.CreateICmpSGT(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_initial"),
                                         ConstantInt::get(int_type, 0), "arg_is_positive");

    // Store into arg_is_positive_ptr
    builder.CreateStore(check, arg_is_positive_ptr);

    builder.CreateCondBr(check, handle_integer_part, handle_negative_arg);
  }

  // ----------------------------------------------------
  // Handle the integer part.
  builder.SetInsertPoint(handle_integer_part);
  {
    Value *result = builder.CreateLoad(getElementTypeFromValuePointer(one_ptr_ret.value), one_ptr_ret.value, "one");
    Value *left_shifted_result = builder.CreateShl(result, integer_part, "one_left_shifted_int");
    Value *right_shifted_result = builder.CreateLShr(result, integer_part, "one_right_shifted_int");

    Value *arg_is_positive = builder.CreateLoad(getElementTypeFromValuePointer(arg_is_positive_ptr), arg_is_positive_ptr, "arg_is_positive");

    // Depending on the sign, shift left or right

    result = builder.CreateSelect(
        arg_is_positive,
        left_shifted_result, right_shifted_result, "result_shifted_integer");

    // Store the result
    builder.CreateStore(result, return_value_ptr);
  }
  builder.CreateBr(handle_fractional_part);


  // ----------------------------------------------------
  // Fractional part loop boundaries.
  builder.SetInsertPoint(handle_fractional_part);
  {
    // Check loop boundaries
    Value *check = builder.CreateICmpSLT(builder.CreateLoad(getElementTypeFromValuePointer(i_ptr), i_ptr, "i"),
                                         ConstantInt::get(int_type, flttofix::exp2_Taylor_expansion_terms), "check_loop_boundaries");

    builder.CreateCondBr(check, fractional_part_loop_body, end);
  }

  // ----------------------------------------------------
  // Fractional part loop body.
  builder.SetInsertPoint(fractional_part_loop_body);
  {
    Value *result = builder.CreateLoad(getElementTypeFromValuePointer(one_ptr_ret.value), one_ptr_ret.value, "one");
    Value *left_shifted_result = builder.CreateShl(result, integer_part, "one_left_shifted_int");
    Value *right_shifted_result = builder.CreateLShr(result, integer_part, "one_right_shifted_int");

    Value *arg_is_positive = builder.CreateLoad(getElementTypeFromValuePointer(arg_is_positive_ptr), arg_is_positive_ptr, "arg_is_positive");

    // Depending on the sign, shift left or right

    result = builder.CreateSelect(
        arg_is_positive,
        left_shifted_result, right_shifted_result, "result_shifted_integer");

    // Store the result
    builder.CreateStore(result, return_value_ptr);
  }


  LLVM_DEBUG(dbgs() << "End of exp2 routine"
                    << "\n");

  LLVM_DEBUG(dbgs() << "x_ptr.value before shift: ");
  x_ptr.value->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // At this point x and y should both be equal to the result of the CORDIC algorithm. We return x.

  auto ret = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_value_final");

  LLVM_DEBUG(dbgs() << "ret: ");
  ret->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // Shift right the result to realign the fractional part
  // builder.CreateLShr(arg_ptr, internal_fxpt.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt(), "output");
  output_temp = builder.CreateAShr(ret, ConstantInt::get(int_type_wide, internal_fxpt.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), "arg_value_final_shifted");

  LLVM_DEBUG(dbgs() << "output_temp after shift: ");
  output_temp->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // Allocate return value

  output_temp = builder.CreateTrunc(output_temp, int_type_narrow, "output");
  LLVM_DEBUG(dbgs() << "output_temp: ");
  return_value_ptr->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  builder.CreateStore(output_temp, return_value_ptr);

  builder.CreateBr(end);
  builder.SetInsertPoint(end);
  builder.CreateRet(builder.CreateLoad(getElementTypeFromValuePointer(return_value_ptr), return_value_ptr));
  return true;
}

} // namespace flttofix
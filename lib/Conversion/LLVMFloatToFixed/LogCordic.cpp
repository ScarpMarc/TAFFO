/*
    Hyperbolic CORDIC for log
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

bool createLog(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  //
  newfs->deleteBody();

  Module *M = oldf->getParent();

  // Check if the function is log1p = log(1+x)
  bool isLogp1 =
      oldf->getName().find("log1p") == 0;
  LLVM_DEBUG(dbgs() << "is log1p: " << isLogp1 << "\n");

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

  // ----------------------------------------------------

  auto int_type = fxparg.scalarToLLVMType(cont);

  // Pointer to the argument
  Value *arg_ptr = builder.CreateAlloca(int_type, nullptr, "arg");
  builder.CreateStore(newfs->getArg(0), arg_ptr);

  LLVM_DEBUG(dbgs() << "arg_ptr: ");
  arg_ptr->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // If the argument is unsigned, make it signed
  if (!fxparg.scalarIsSigned()) {
    LLVM_DEBUG(dbgs() << "Argument is unsigned: shifting it to the right by 1 bit\n");
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), ConstantInt::get(int_type, 1), "unsigned_arg_shifted"), arg_ptr);
    fxparg.scalarFracBitsAmt() = fxparg.scalarFracBitsAmt() - 1;
    fxparg.scalarIsSigned() = true;
  }

  /*
    Define LLVM integer types that will hold our variables.
    The internal variables will have a similar magnitude to the argument, so we can use the same data type with an additional bit for the integer part.
  */
  auto internal_fxpt = flttofix::FixedPointType(true, fxparg.scalarFracBitsAmt() - 1, fxparg.scalarBitsAmt());
  LLVM_DEBUG(dbgs() << "Internal fixed point type: ");
  int_type->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // Generate strings for constants names
  std::string S_ret_point = "." + std::to_string(fxpret.scalarFracBitsAmt());
  std::string S_int_point = "." + std::to_string(internal_fxpt.scalarFracBitsAmt());


  auto truefxpret = fxpret;
  /*
  The largest arcatanh constant we have to use is about 3.2. Internally, we use the return's type; the problem is that if the return's fixed point type has very few integer bits, we may not have enough to represent the various constants.
  Thus, we must make sure that we have at least 2 integer bits +1 for the sign
  */
  if ((fxpret.scalarBitsAmt() - fxpret.scalarFracBitsAmt()) < 3) {
    fxpret = flttofix::FixedPointType(true,
                                      fxpret.scalarBitsAmt() - 3,
                                      fxpret.scalarBitsAmt());
    LLVM_DEBUG(dbgs() << "New fxpret: " << fxpret << "\n");
  }

  // ----------------------------------------------------
  // Basic blocks

  // Block for the initialization of the loop
  BasicBlock *init = BasicBlock::Create(cont, "init", newfs);

  // Blocks where we check loop boundaries
  BasicBlock *check_loop_negatives = BasicBlock::Create(cont, "check_loop_negatives", newfs);
  BasicBlock *check_loop_positives = BasicBlock::Create(cont, "check_loop_positives", newfs);

  // Main loop bodies
  BasicBlock *loop_body_negatives = BasicBlock::Create(cont, "loop_body_negatives", newfs);
  BasicBlock *loop_body_positives = BasicBlock::Create(cont, "loop_body_positives", newfs);

  // In case we did not need to return a special value, we will cast the result to the return type here
  BasicBlock *finalize = BasicBlock::Create(cont, "finalize", newfs);

  // Return block
  BasicBlock *return_point = BasicBlock::Create(cont, "Special", newfs);

  // End block, which returns the result
  BasicBlock *end = BasicBlock::Create(cont, "end", newfs);


  LLVM_DEBUG(dbgs() << "Create init"
                    << "\n");
  builder.CreateBr(init);
  builder.SetInsertPoint(init);

  // ----------------------------------------------------
  // Support variables that we use internally
  // The argument is created above
  TaffoMath::pair_ftp_value<llvm::Value *> x_ptr(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Value *> y_ptr(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Value *> z_ptr(fxpret);
  x_ptr.value = builder.CreateAlloca(int_type, nullptr, "x");
  y_ptr.value = builder.CreateAlloca(int_type, nullptr, "y");
  z_ptr.value = builder.CreateAlloca(int_type, nullptr, "z");

  // Pointer to the current iteration counter
  Value *i_ptr = builder.CreateAlloca(int_type, nullptr, "i_ptr");

  // Pointer to zero in the internal fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_arg(internal_fxpt);
  // Pointer to one in the internal fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> one(internal_fxpt);
  // Pointer to zero in the return fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_ret(fxpret);
  // The arctanh array table
  TaffoMath::pair_ftp_value<llvm::Constant *,
                            TaffoMath::TABLELENGHT>
      arctanh_2power;

  // ----------------------------------------------------

  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, internal_fxpt, zero_arg.value, zero_arg.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::one, internal_fxpt, one.value, one.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, fxpret, zero_ret.value, zero_ret.fpt);

  zero_arg.value = TaffoMath::createGlobalConst(
      M, "zero_arg" + S_int_point, zero_arg.fpt.scalarToLLVMType(cont), zero_arg.value,
      dataLayout.getPrefTypeAlignment(zero_arg.fpt.scalarToLLVMType(cont)));

  one.value = TaffoMath::createGlobalConst(
      M, "one" + S_int_point, one.fpt.scalarToLLVMType(cont), one.value,
      dataLayout.getPrefTypeAlignment(one.fpt.scalarToLLVMType(cont)));

  zero_ret.value = TaffoMath::createGlobalConst(
      M, "zero_ret" + S_ret_point, zero_ret.fpt.scalarToLLVMType(cont), zero_ret.value,
      dataLayout.getPrefTypeAlignment(zero_ret.fpt.scalarToLLVMType(cont)));


  // ----------------------------------------------------
  // Create the table for arctanh

  LLVM_DEBUG(dbgs() << "\n===== Create arctanh table ====="
                    << "\n");

  llvm::AllocaInst *pointer_to_arctanh_array = nullptr;

  for (int i = 0; i < TaffoMath::TABLELENGHT; i++) {
    LLVM_DEBUG(dbgs() << "Element " << i << ":\n");
    arctanh_2power.fpt.push_back(flttofix::FixedPointType(fxpret));
    Constant *tmp = nullptr;
    auto &current_fpt = arctanh_2power.fpt.front();
    TaffoMath::createFixedPointFromConst(
        cont, ref, flttofix::arctanh_2power[i], fxpret, tmp, current_fpt);
    arctanh_2power.value.push_back(tmp);
    LLVM_DEBUG(dbgs() << "\n");
  }

  auto arctanhArrayType = llvm::ArrayType::get(arctanh_2power.value[0]->getType(),
                                               TaffoMath::TABLELENGHT);
  LLVM_DEBUG(dbgs() << "arctanhArrayType: ");
  arctanhArrayType->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  auto arctanhConstArray = llvm::ConstantArray::get(
      arctanhArrayType, llvm::ArrayRef<llvm::Constant *>(arctanh_2power.value));

  LLVM_DEBUG(dbgs() << "arctanhConstArray: ");
  arctanhArrayType->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  auto alignement_arctanh =
      dataLayout.getPrefTypeAlignment(arctanh_2power.value[0]->getType());
  auto arctan_g =
      TaffoMath::createGlobalConst(M, "arctanh_g." + std::to_string(fxpret.scalarFracBitsAmt()), arctanhArrayType,
                                   arctanhConstArray, alignement_arctanh);

  pointer_to_arctanh_array = builder.CreateAlloca(arctanhArrayType, nullptr, "arctanh_array");
  pointer_to_arctanh_array->setAlignment(llvm::Align(alignement_arctanh));

  builder.CreateMemCpy(
      pointer_to_arctanh_array, llvm::Align(alignement_arctanh), arctan_g, llvm::Align(alignement_arctanh),
      TaffoMath::TABLELENGHT * (int_type->getScalarSizeInBits() >> 3));
  LLVM_DEBUG(dbgs() << "\nAdd to newf arctanh table. Copied " << TaffoMath::TABLELENGHT * (int_type->getScalarSizeInBits() >> 3) << " bytes\n");

  // If the argument is negative, return a special value
  {
    // Shift right arg by 1
    auto arg_value = builder.CreateAShr(
        builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_value"),
        ConstantInt::get(int_type, 1),
        "arg_value_shr_1");
    // Store arg_value in arg_ptr
    builder.CreateStore(arg_value, arg_ptr);

    // Create two blocks: one for the negative case (BTrue) and one for the positive or zero case (BFalse)
    BasicBlock *BTrue = BasicBlock::Create(cont, "Special", newfs);
    BasicBlock *BFalse = BasicBlock::Create(cont, "body", newfs);

    // If the called function is log1p add 1 to the argument
    if (isLogp1) {
      arg_value = builder.CreateAdd(
          arg_value,
          builder.CreateLoad(getElementTypeFromValuePointer(one.value), one.value, "one"));
      builder.CreateStore(arg_value, arg_ptr);
    }

    // Create a conditional branch based on the sign check
    Value *check_sign = builder.CreateICmpSLE(
        arg_value,                    // Confronta l'argomento caricato
        ConstantInt::get(int_type, 0) // Confronta con zero per verificare il segno negativo
    );

    builder.CreateCondBr(check_sign, BTrue, BFalse);
    // If negative, handle in BTrue
    builder.SetInsertPoint(BTrue);
    // Calculate the value of the most negative number (-2^(n-1)) for a signed integer
    Value *negative_max = ConstantInt::get(int_type, APInt::getSignedMinValue(truefxpret.scalarBitsAmt()));
    // Store the negative max value in z_ptr.value
    builder.CreateStore(negative_max, z_ptr.value);
    // Jump to the return block (return_point)
    builder.CreateBr(return_point);
    // Handle the non-negative case (BFalse)
    builder.SetInsertPoint(BFalse);
  }


  // calculate log

  LLVM_DEBUG(dbgs() << "Starting log routine"
                    << "\n");

  auto zero_arg_value = builder.CreateLoad(getElementTypeFromValuePointer(zero_arg.value), zero_arg.value, "zero_arg");
  LLVM_DEBUG(dbgs() << "zero: ");
  zero_arg_value->print(dbgs(), true);
  auto zero_ret_value = builder.CreateLoad(getElementTypeFromValuePointer(zero_ret.value), zero_ret.value, "zero_ret");
  LLVM_DEBUG(dbgs() << "\n");

  LLVM_DEBUG(dbgs() << "Zero value set"
                    << "\n");

  auto one_value = builder.CreateLoad(getElementTypeFromValuePointer(one.value), one.value, "one");
  auto arg_value = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_value");

  // Initialise x y z
  // x=arg+1
  builder.CreateStore(builder.CreateAdd(arg_value, one_value), x_ptr.value);
  // y=arg-1
  builder.CreateStore(builder.CreateSub(arg_value, one_value), y_ptr.value);
  // z=0
  builder.CreateStore(zero_ret_value, z_ptr.value);

  LLVM_DEBUG(dbgs() << "Initial x y z set"
                    << "\n");

  // Temp values to store updates
  Value *x_update;
  Value *y_update;
  Value *z_update;

  LLVM_DEBUG(dbgs() << "Initial blocks set"
                    << "\n");

  /*
    We need to iterate from -m to 0 and then from 1 to n.

    We first loop on the negative values, then we loop on the positive values.
    The table is the same.
  */

  // NEGATIVE LOOP

  LLVM_DEBUG(dbgs() << "Start negative loop"
                    << "\n");

  builder.CreateStore(zero_ret_value, i_ptr);

  LLVM_DEBUG(dbgs() << "Iterator set"
                    << "\n");

  builder.CreateBr(check_loop_negatives);
  builder.SetInsertPoint(check_loop_negatives);

  auto i_value = builder.CreateLoad(getElementTypeFromValuePointer(i_ptr), i_ptr, "i_value_loop1");

  // Check whether i < m; if so, go to loop body. Else, go to positive loop.
  Value *iIsLessThanM = builder.CreateICmpSLE(
      i_value,
      ConstantInt::get(int_type, flttofix::cordic_exp_negative_iterations), "loop_condition_negatives");

  // Execute the loop if i < m; else, go to the positive loop.
  builder.CreateCondBr(iIsLessThanM, loop_body_negatives,
                       check_loop_positives);
  {
    builder.SetInsertPoint(loop_body_negatives);

    LLVM_DEBUG(dbgs() << "Start negative loop body"
                      << "\n");

    // Current x y z values
    auto x_value = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_curr_loop1");
    auto y_value = builder.CreateLoad(getElementTypeFromValuePointer(y_ptr.value), y_ptr.value, "y_curr_loop1");
    auto z_value = builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value, "z_curr_loop1");

    // sign = y >= 0 ? 1 : -1;
    Value *update_sign = builder.CreateSelect(
        builder.CreateICmpSGE(y_value, zero_arg_value, "y_is_positive_loop2"),
        ConstantInt::get(int_type, 1), ConstantInt::get(int_type, -1), "update_sign_loop2");

    // update_sign > 0 ?
    auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_arg_value, "update_sign_greater_zero_loop2");

    LLVM_DEBUG(dbgs() << "Sign greater than zero set"
                      << "\n");

    /*
      shift_amt = cordic_exp_negative_iterations+2-i (casted to larger type since otherwise LLVM will complain)
      The original loop should compute 2^(-i+2), with i going from -m to 0. However our i starts from 0,
        so we need to compute 2^(m^2-i) instead and then shift right later.
     */
    Value *shift_amt = builder.CreateSub(
        ConstantInt::get(int_type, flttofix::cordic_exp_negative_iterations + 2), i_value, "shift_amt_loop1");

    LLVM_DEBUG(dbgs() << "Shift amount set"
                      << "\n");

    {
      // Update y. The update reads x.

      // Calculate x * (2 ^ -shift_amt)
      y_update = builder.CreateAShr(
          x_value, shift_amt, "y_upd_1_loop1");

      LLVM_DEBUG(dbgs() << "y_update 1 calculated"
                        << "\n");

      // Calculate x - x * (2 ^ -shift_amt)
      y_update = builder.CreateSub(
          x_value, y_update, "y_upd_2_loop1");

      LLVM_DEBUG(dbgs() << "y_update 2 calculated"
                        << "\n");

      // Calculate (update_sign > 0 ? -(x - x * (2 ^ -shift_amt)) : (x - x * (2 ^ -shift_amt)));
      y_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg_value, y_update, "minus_y_upd_2_loop1"), y_update, "y_upd_3_loop1");

      LLVM_DEBUG(dbgs() << "y_update 3 calculated"
                        << "\n");

      // y_{k+1} = y_k + y_update. Set to temp value since we will need to use y next.
      y_update = builder.CreateAdd(
          y_value, y_update, "y_upd_4_loop1");

      LLVM_DEBUG(dbgs() << "y_update 4 calculated"
                        << "\n");
    }

    {
      // Update x. The update reads y.

      // Calculate y * (2 ^ -shift_amt)
      x_update = builder.CreateAShr(
          y_value, shift_amt, "x_upd_1_loop1");

      LLVM_DEBUG(dbgs() << "x_update 1 calculated"
                        << "\n");

      // Calculate y - y * (2 ^ -shift_amt)
      x_update = builder.CreateSub(
          y_value, x_update, "x_upd_2_loop1");

      LLVM_DEBUG(dbgs() << "x_update 2 calculated"
                        << "\n");

      // Calculate (update_sign > 0 ? -(y - y * (2 ^ -shift_amt)) : (y - y * (2 ^ -shift_amt)));
      x_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg_value, x_update, "minus_x_upd_2_loop1"), x_update, "x_upd_3_loop1");

      LLVM_DEBUG(dbgs() << "x_update 3 calculated"
                        << "\n");

      // x_{k+1} = x_k + x_update
      x_update =
          builder.CreateAdd(x_value, x_update, "x_upd_4_loop1");

      LLVM_DEBUG(dbgs() << "x_update 4 calculated"
                        << "\n");
    }

    // Store y_update into y
    builder.CreateStore(y_update, y_ptr.value);

    LLVM_DEBUG(dbgs() << "y_update stored"
                      << "\n");

    // Store x_update into x
    builder.CreateStore(x_update, x_ptr.value);

    LLVM_DEBUG(dbgs() << "x_update stored"
                      << "\n");

    /*
      The two parts where we update z and increment the counter are identical for the negative and positive loops and could theoretically be made into a single subroutine.
      However, we want to avoid checking where we are each time, so we duplicate the code.
    */

    {
      // Update z

      // Calculate arctanh_2power[i]
      z_update = builder.CreateGEP(
          getElementTypeFromValuePointer(pointer_to_arctanh_array), pointer_to_arctanh_array,
          {zero_ret_value, i_value}, "atanh_2pwr_i_ptr_loop1");

      LLVM_DEBUG(dbgs() << "z_update: ");
      z_update->print(dbgs(), true);
      LLVM_DEBUG(dbgs() << "\n");

      LLVM_DEBUG(dbgs() << "z_update 1 calculated"
                        << "\n");

      z_update = builder.CreateLoad(getElementTypeFromValuePointer(z_update), z_update, "atanh_2pwr_i_loop1");

      LLVM_DEBUG(dbgs() << "z_update 2 calculated"
                        << "\n");

      // z_update = (update_sign > 0 ? arctanh_2power[i] : -arctanh_2power[i]);
      z_update = builder.CreateSelect(
          update_sign_greater_zero, z_update, builder.CreateSub(zero_ret_value, z_update, "minus_atanh_2pwr_i_loop1"), "arg_update_loop1");

      LLVM_DEBUG(dbgs() << "z_update 3 calculated"
                        << "\n");

      // z_{k+1} = z + z_update
      builder.CreateStore(
          builder.CreateAdd(z_value, z_update, "arg_increment_loop1"), z_ptr.value);

      LLVM_DEBUG(dbgs() << "z_update stored"
                        << "\n");
    }

    // i++
    builder.CreateStore(builder.CreateAdd(i_value,
                                          ConstantInt::get(int_type, 1), "iterator_value_next_loop1"),
                        i_ptr);

    LLVM_DEBUG(dbgs() << "i incremented"
                      << "\n");
    builder.CreateBr(check_loop_negatives);
  }

  // POSITIVE LOOP

  // builder.CreateBr(check_loop_positives);
  builder.SetInsertPoint(check_loop_positives);

  LLVM_DEBUG(dbgs() << "Start positive loop"
                    << "\n");

  // TODO: repeat iterations 4, 13, 40

  i_value = builder.CreateLoad(getElementTypeFromValuePointer(i_ptr), i_ptr, "i_value_loop2");

  // Check whether i < (m+n); if so, go to loop body. Else, go to positive loop.
  Value *iIsLessThanN = builder.CreateICmpSLT(
      i_value,
      ConstantInt::get(int_type, flttofix::cordic_exp_total_iterations), "loop_condition_positives");

  // Execute the loop if i < m+n; else, go to the end of the function.
  builder.CreateCondBr(iIsLessThanN, loop_body_positives,
                       finalize);
  {
    builder.SetInsertPoint(loop_body_positives);

    LLVM_DEBUG(dbgs() << "Start positive loop body"
                      << "\n");


    // Current x y z values
    auto x_value = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_curr_loop2");
    auto y_value = builder.CreateLoad(getElementTypeFromValuePointer(y_ptr.value), y_ptr.value, "y_curr_loop2");
    auto z_value = builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value, "z_curr_loop2");


    // sign = y >= 0 ? 1 : -1;
    Value *update_sign = builder.CreateSelect(
        builder.CreateICmpSGE(y_value, zero_arg_value, "arg_is_negative_loop2"),
        ConstantInt::get(int_type, 1), ConstantInt::get(int_type, -1), "update_sign_loop2");

    // update_sign > 0 ?
    auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_arg_value, "update_sign_greater_zero_loop2");

    // shift_amt = i-m since we do not reset i (again, casted to larger type since otherwise LLVM will complain)
    Value *shift_amt = builder.CreateSub(i_value,
                                         ConstantInt::get(int_type, flttofix::cordic_exp_negative_iterations), "shift_amt_loop2");

    LLVM_DEBUG(dbgs() << "Shift amount set"
                      << "\n");

    {
      // Update y. The update reads x.

      // Calculate x * (2 ^ -shift_amt)
      y_update = builder.CreateAShr(
          x_value, shift_amt, "y_upd_1_loop2");

      LLVM_DEBUG(dbgs() << "y_update 1 calculated"
                        << "\n");

      // Calculate (update_sign > 0 ? -(x * (2 ^ -shift_amt)) : (x * (2 ^ -shift_amt)));
      y_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg_value, y_update, "minus_y_upd_1_loop2"), y_update, "y_upd_2_loop2");

      LLVM_DEBUG(dbgs() << "y_update 2 calculated"
                        << "\n");

      // y_{k+1} = y_k + y_update. Set to temp value since we will need to use y next.
      y_update = builder.CreateAdd(
          y_value, y_update, "y_upd_3_loop2");

      LLVM_DEBUG(dbgs() << "y_update 3 calculated"
                        << "\n");
    }

    {
      // Update x. The update reads y.

      // Calculate y * (2 ^ -shift_amt)
      x_update = builder.CreateAShr(
          y_value, shift_amt, "x_upd_1_loop2");

      LLVM_DEBUG(dbgs() << "x_update 1 calculated"
                        << "\n");

      // Calculate (update_sign > 0 ? -(y * (2 ^ -shift_amt)) : (y * (2 ^ -shift_amt)));
      x_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg_value, x_update, "minus_x_upd_1_loop2"), x_update, "x_upd_2_loop2");

      LLVM_DEBUG(dbgs() << "x_update 2 calculated"
                        << "\n");

      // x_{k+1} = x_k + x_update
      x_update =
          builder.CreateAdd(x_value, x_update, "x_upd_3_loop2");

      LLVM_DEBUG(dbgs() << "x_update 3 calculated"
                        << "\n");
    }

    // Store y_update into y
    builder.CreateStore(y_update, y_ptr.value);

    // Store x_update into x
    builder.CreateStore(x_update, x_ptr.value);

    LLVM_DEBUG(dbgs() << "x and y updated"
                      << "\n");

    /*
      The two parts where we update z and increment the counter are identical for the negative and positive loops and could theoretically be made into a single subroutine.
      However, we want to avoid checking where we are each time, so we duplicate the code.
    */

    {
      // Update z

      // Calculate arctanh_2power[i]
      z_update = builder.CreateGEP(getElementTypeFromValuePointer(pointer_to_arctanh_array), pointer_to_arctanh_array,
                                   {zero_ret_value, i_value}, "atanh_2pwr_i_ptr_loop2");

      LLVM_DEBUG(dbgs() << "z_update: ");
      z_update->print(dbgs(), true);
      LLVM_DEBUG(dbgs() << "\n");

      LLVM_DEBUG(dbgs() << "z_update 1 calculated"
                        << "\n");

      z_update = builder.CreateLoad(getElementTypeFromValuePointer(z_update), z_update, "atanh_2pwr_i_loop2");

      LLVM_DEBUG(dbgs() << "z_update 2 calculated"
                        << "\n");

      // z = z + (update_sign > 0 ? -arctanh_2power[i] : arctanh_2power[i]);
      z_update = builder.CreateSelect(
          update_sign_greater_zero, z_update, builder.CreateSub(zero_arg_value, z_update), "arg_update_loop2");

      LLVM_DEBUG(dbgs() << "z_update 3 calculated"
                        << "\n");

      // z_{k+1} = z_k + z_update
      builder.CreateStore(
          builder.CreateAdd(z_value, z_update, "arg_increment_loop2"), z_ptr.value);

      LLVM_DEBUG(dbgs() << "z_update stored"
                        << "\n");
    }

    // i++
    builder.CreateStore(builder.CreateAdd(i_value,
                                          ConstantInt::get(int_type, 1), "iterator_value_next_loop2"),
                        i_ptr);
    builder.CreateBr(check_loop_positives);

    // Set the insert point to the end of the function, which is after the else.
    builder.SetInsertPoint(finalize);
  }

  LLVM_DEBUG(dbgs() << "End of log routine"
                    << "\n");

  // z_final = 2*z where z =1/2*ln(arg)
  builder.CreateStore(
      builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value), ConstantInt::get(int_type, 1), "value_final_shifted_left"), z_ptr.value);

  if (fxpret.scalarFracBitsAmt() < truefxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value), truefxpret.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), z_ptr.value);
  }

  builder.CreateBr(return_point);
  builder.SetInsertPoint(return_point);

  auto return_value = builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value, "z_value_final");

  LLVM_DEBUG(dbgs() << "return_value after shift: ");
  return_value->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  builder.CreateBr(end);
  builder.SetInsertPoint(end);
  builder.CreateRet(return_value);
  // builder.SetInsertPoint(undefined);
  // llvm_unreachable("Undefined behavior");
  return true;
}

bool createLog10(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
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

  // ----------------------------------------------------

  auto int_type = fxparg.scalarToLLVMType(cont);

  // Pointer to the argument
  Value *arg_ptr = builder.CreateAlloca(int_type, nullptr, "arg");
  builder.CreateStore(newfs->getArg(0), arg_ptr);

  LLVM_DEBUG(dbgs() << "arg_ptr: ");
  arg_ptr->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // If the argument is unsigned, make it signed
  if (!fxparg.scalarIsSigned()) {
    LLVM_DEBUG(dbgs() << "Argument is unsigned: shifting it to the right by 1 bit\n");
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), ConstantInt::get(int_type, 1), "unsigned_arg_shifted"), arg_ptr);
    fxparg.scalarFracBitsAmt() = fxparg.scalarFracBitsAmt() - 1;
    fxparg.scalarIsSigned() = true;
  }


  /*
    Define LLVM integer types that will hold our variables.
    The internal variables will have a similar magnitude to the argument, so we can use the same data type with an additional bit for the integer part.
  */
  auto internal_fxpt = flttofix::FixedPointType(true, fxparg.scalarFracBitsAmt() - 1, fxparg.scalarBitsAmt());
  LLVM_DEBUG(dbgs() << "Internal fixed point type: ");
  int_type->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // Generate strings for constants names
  std::string S_ret_point = "." + std::to_string(fxpret.scalarFracBitsAmt());
  std::string S_int_point = "." + std::to_string(internal_fxpt.scalarFracBitsAmt());


  auto truefxpret = fxpret;
  /*
  The largest arcatanh constant we have to use is about 1.4. Internally, we use the return's type; the problem is that if the return's fixed point type has very few integer bits, we may not have enough to represent the various constants.
  Thus, we must make sure that we have at least 1 integer bits +1 for the sign
  */
  if ((fxpret.scalarBitsAmt() - fxpret.scalarFracBitsAmt()) < 2) {
    fxpret = flttofix::FixedPointType(true,
                                      fxpret.scalarBitsAmt() - 2,
                                      fxpret.scalarBitsAmt());
    LLVM_DEBUG(dbgs() << "New fxpret: " << fxpret << "\n");
  }

  // ----------------------------------------------------
  // Basic blocks

  // Block for the initialization of the loop
  BasicBlock *init = BasicBlock::Create(cont, "init", newfs);

  // Blocks where we check loop boundaries
  BasicBlock *check_loop_negatives = BasicBlock::Create(cont, "check_loop_negatives", newfs);
  BasicBlock *check_loop_positives = BasicBlock::Create(cont, "check_loop_positives", newfs);

  // Main loop bodies
  BasicBlock *loop_body_negatives = BasicBlock::Create(cont, "loop_body_negatives", newfs);
  BasicBlock *loop_body_positives = BasicBlock::Create(cont, "loop_body_positives", newfs);

  // In case we did not need to return a special value, we will cast the result to the return type here
  BasicBlock *finalize = BasicBlock::Create(cont, "finalize", newfs);

  // Return block
  BasicBlock *return_point = BasicBlock::Create(cont, "Special", newfs);

  // End block, which returns the result
  BasicBlock *end = BasicBlock::Create(cont, "end", newfs);


  LLVM_DEBUG(dbgs() << "Create init"
                    << "\n");
  builder.CreateBr(init);
  builder.SetInsertPoint(init);

  // ----------------------------------------------------
  // Support variables that we use internally
  // The argument is created above
  TaffoMath::pair_ftp_value<llvm::Value *> x_ptr(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Value *> y_ptr(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Value *> z_ptr(fxpret);
  x_ptr.value = builder.CreateAlloca(int_type, nullptr, "x");
  y_ptr.value = builder.CreateAlloca(int_type, nullptr, "y");
  z_ptr.value = builder.CreateAlloca(int_type, nullptr, "z");

  // Pointer to the current iteration counter
  Value *i_ptr = builder.CreateAlloca(int_type, nullptr, "i_ptr");

  // Pointer to zero in the internal fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_arg(internal_fxpt);
  // Pointer to one in the internal fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> one(internal_fxpt);
  // Pointer to zero in the return fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_ret(fxpret);
  // The arctanh array table
  TaffoMath::pair_ftp_value<llvm::Constant *,
                            TaffoMath::TABLELENGHT>
      arctanh_2power_10;

  // ----------------------------------------------------

  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, internal_fxpt, zero_arg.value, zero_arg.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::one, internal_fxpt, one.value, one.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, fxpret, zero_ret.value, zero_ret.fpt);

  zero_arg.value = TaffoMath::createGlobalConst(
      M, "zero_arg" + S_int_point, zero_arg.fpt.scalarToLLVMType(cont), zero_arg.value,
      dataLayout.getPrefTypeAlignment(zero_arg.fpt.scalarToLLVMType(cont)));

  one.value = TaffoMath::createGlobalConst(
      M, "one" + S_int_point, one.fpt.scalarToLLVMType(cont), one.value,
      dataLayout.getPrefTypeAlignment(one.fpt.scalarToLLVMType(cont)));

  zero_ret.value = TaffoMath::createGlobalConst(
      M, "zero_ret" + S_ret_point, zero_ret.fpt.scalarToLLVMType(cont), zero_ret.value,
      dataLayout.getPrefTypeAlignment(zero_ret.fpt.scalarToLLVMType(cont)));


  // ----------------------------------------------------
  // Create the table for arctanh

  LLVM_DEBUG(dbgs() << "\n===== Create arctanh table ====="
                    << "\n");

  llvm::AllocaInst *pointer_to_arctanh_array = nullptr;

  for (int i = 0; i < TaffoMath::TABLELENGHT; i++) {
    LLVM_DEBUG(dbgs() << "Element " << i << ":\n");
    arctanh_2power_10.fpt.push_back(flttofix::FixedPointType(fxpret));
    Constant *tmp = nullptr;
    auto &current_fpt = arctanh_2power_10.fpt.front();
    TaffoMath::createFixedPointFromConst(
        cont, ref, flttofix::arctanh_2power_10[i], fxpret, tmp, current_fpt);
    arctanh_2power_10.value.push_back(tmp);
    LLVM_DEBUG(dbgs() << "\n");
  }

  auto arctanhArrayType = llvm::ArrayType::get(arctanh_2power_10.value[0]->getType(),
                                               TaffoMath::TABLELENGHT);
  LLVM_DEBUG(dbgs() << "arctanhArrayType: ");
  arctanhArrayType->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  auto arctanhConstArray = llvm::ConstantArray::get(
      arctanhArrayType, llvm::ArrayRef<llvm::Constant *>(arctanh_2power_10.value));

  LLVM_DEBUG(dbgs() << "arctanhConstArray: ");
  arctanhArrayType->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  auto alignement_arctanh =
      dataLayout.getPrefTypeAlignment(arctanh_2power_10.value[0]->getType());
  auto arctan_g =
      TaffoMath::createGlobalConst(M, "arctanh_g." + std::to_string(fxpret.scalarFracBitsAmt()), arctanhArrayType,
                                   arctanhConstArray, alignement_arctanh);

  pointer_to_arctanh_array = builder.CreateAlloca(arctanhArrayType, nullptr, "arctanh_array");
  pointer_to_arctanh_array->setAlignment(llvm::Align(alignement_arctanh));

  builder.CreateMemCpy(
      pointer_to_arctanh_array, llvm::Align(alignement_arctanh), arctan_g, llvm::Align(alignement_arctanh),
      TaffoMath::TABLELENGHT * (int_type->getScalarSizeInBits() >> 3));
  LLVM_DEBUG(dbgs() << "\nAdd to newf arctanh table. Copied " << TaffoMath::TABLELENGHT * (int_type->getScalarSizeInBits() >> 3) << " bytes\n");

  // If the argument is negative, return a special value
  {
    // Shift right arg by 1
    auto arg_value = builder.CreateAShr(
        builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_value"),
        ConstantInt::get(int_type, 1),
        "arg_value_shr_1");
    // Store arg_value in arg_ptr
    builder.CreateStore(arg_value, arg_ptr);

    // Create two blocks: one for the negative case (BTrue) and one for the positive or zero case (BFalse)
    BasicBlock *BTrue = BasicBlock::Create(cont, "Special", newfs);
    BasicBlock *BFalse = BasicBlock::Create(cont, "body", newfs);

    // Create a conditional branch based on the sign check
    Value *check_sign = builder.CreateICmpSLE(
        arg_value,                    // Confronta l'argomento caricato
        ConstantInt::get(int_type, 0) // Confronta con zero per verificare il segno negativo
    );

    builder.CreateCondBr(check_sign, BTrue, BFalse);
    // If negative, handle in BTrue
    builder.SetInsertPoint(BTrue);
    // Calculate the value of the most negative number (-2^(n-1)) for a signed integer
    Value *negative_max = ConstantInt::get(int_type, APInt::getSignedMinValue(truefxpret.scalarBitsAmt()));
    // Store the negative max value in z_ptr.value
    builder.CreateStore(negative_max, z_ptr.value);
    // Jump to the return block (return_point)
    builder.CreateBr(return_point);
    // Handle the non-negative case (BFalse)
    builder.SetInsertPoint(BFalse);
  }

  // calculate log10

  LLVM_DEBUG(dbgs() << "Starting ln routine"
                    << "\n");

  auto zero_arg_value = builder.CreateLoad(getElementTypeFromValuePointer(zero_arg.value), zero_arg.value, "zero_arg");
  LLVM_DEBUG(dbgs() << "zero: ");
  zero_arg_value->print(dbgs(), true);
  auto zero_ret_value = builder.CreateLoad(getElementTypeFromValuePointer(zero_ret.value), zero_ret.value, "zero_ret");
  LLVM_DEBUG(dbgs() << "\n");

  LLVM_DEBUG(dbgs() << "Zero value set"
                    << "\n");

  auto one_value = builder.CreateLoad(getElementTypeFromValuePointer(one.value), one.value, "one");
  // Shift right arg_value by 1
  auto arg_value = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_value");

  // Initialise x y z
  // x=arg+1
  builder.CreateStore(builder.CreateAdd(arg_value, one_value), x_ptr.value);
  // y=arg-1
  builder.CreateStore(builder.CreateSub(arg_value, one_value), y_ptr.value);
  // z=0
  builder.CreateStore(zero_ret_value, z_ptr.value);

  LLVM_DEBUG(dbgs() << "Initial x y z set"
                    << "\n");

  // Temp values to store updates
  Value *x_update;
  Value *y_update;
  Value *z_update;

  LLVM_DEBUG(dbgs() << "Initial blocks set"
                    << "\n");

  /*
    We need to iterate from -m to 0 and then from 1 to n.

    We first loop on the negative values, then we loop on the positive values.
    The table is the same.
  */

  // NEGATIVE LOOP

  LLVM_DEBUG(dbgs() << "Start negative loop"
                    << "\n");

  builder.CreateStore(zero_ret_value, i_ptr);

  LLVM_DEBUG(dbgs() << "Iterator set"
                    << "\n");

  builder.CreateBr(check_loop_negatives);
  builder.SetInsertPoint(check_loop_negatives);

  auto i_value = builder.CreateLoad(getElementTypeFromValuePointer(i_ptr), i_ptr, "i_value_loop1");

  // Check whether i < m; if so, go to loop body. Else, go to positive loop.
  Value *iIsLessThanM = builder.CreateICmpSLE(
      i_value,
      ConstantInt::get(int_type, flttofix::cordic_exp_negative_iterations), "loop_condition_negatives");

  // Execute the loop if i < m; else, go to the positive loop.
  builder.CreateCondBr(iIsLessThanM, loop_body_negatives,
                       check_loop_positives);
  {
    builder.SetInsertPoint(loop_body_negatives);

    LLVM_DEBUG(dbgs() << "Start negative loop body"
                      << "\n");

    // Current x y z values
    auto x_value = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_curr_loop1");
    auto y_value = builder.CreateLoad(getElementTypeFromValuePointer(y_ptr.value), y_ptr.value, "y_curr_loop1");
    auto z_value = builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value, "z_curr_loop1");

    // sign = y >= 0 ? 1 : -1;
    Value *update_sign = builder.CreateSelect(
        builder.CreateICmpSGE(y_value, zero_arg_value, "y_is_positive_loop2"),
        ConstantInt::get(int_type, 1), ConstantInt::get(int_type, -1), "update_sign_loop2");

    // update_sign > 0 ?
    auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_arg_value, "update_sign_greater_zero_loop2");

    LLVM_DEBUG(dbgs() << "Sign greater than zero set"
                      << "\n");

    /*
      shift_amt = cordic_exp_negative_iterations+2-i (casted to larger type since otherwise LLVM will complain)
      The original loop should compute 2^(-i+2), with i going from -m to 0. However our i starts from 0,
        so we need to compute 2^(m^2-i) instead and then shift right later.
     */
    Value *shift_amt = builder.CreateSub(
        ConstantInt::get(int_type, flttofix::cordic_exp_negative_iterations + 2), i_value, "shift_amt_loop1");

    LLVM_DEBUG(dbgs() << "Shift amount set"
                      << "\n");

    {
      // Update y. The update reads x.

      // Calculate x * (2 ^ -shift_amt)
      y_update = builder.CreateAShr(
          x_value, shift_amt, "y_upd_1_loop1");

      LLVM_DEBUG(dbgs() << "y_update 1 calculated"
                        << "\n");

      // Calculate x - x * (2 ^ -shift_amt)
      y_update = builder.CreateSub(
          x_value, y_update, "y_upd_2_loop1");

      LLVM_DEBUG(dbgs() << "y_update 2 calculated"
                        << "\n");

      // Calculate (update_sign > 0 ? -(x - x * (2 ^ -shift_amt)) : (x - x * (2 ^ -shift_amt)));
      y_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg_value, y_update, "minus_y_upd_2_loop1"), y_update, "y_upd_3_loop1");

      LLVM_DEBUG(dbgs() << "y_update 3 calculated"
                        << "\n");

      // y_{k+1} = y_k + y_update. Set to temp value since we will need to use y next.
      y_update = builder.CreateAdd(
          y_value, y_update, "y_upd_4_loop1");

      LLVM_DEBUG(dbgs() << "y_update 4 calculated"
                        << "\n");
    }

    {
      // Update x. The update reads y.

      // Calculate y * (2 ^ -shift_amt)
      x_update = builder.CreateAShr(
          y_value, shift_amt, "x_upd_1_loop1");

      LLVM_DEBUG(dbgs() << "x_update 1 calculated"
                        << "\n");

      // Calculate y - y * (2 ^ -shift_amt)
      x_update = builder.CreateSub(
          y_value, x_update, "x_upd_2_loop1");

      LLVM_DEBUG(dbgs() << "x_update 2 calculated"
                        << "\n");

      // Calculate (update_sign > 0 ? -(y - y * (2 ^ -shift_amt)) : (y - y * (2 ^ -shift_amt)));
      x_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg_value, x_update, "minus_x_upd_2_loop1"), x_update, "x_upd_3_loop1");

      LLVM_DEBUG(dbgs() << "x_update 3 calculated"
                        << "\n");

      // x_{k+1} = x_k + x_update
      x_update =
          builder.CreateAdd(x_value, x_update, "x_upd_4_loop1");

      LLVM_DEBUG(dbgs() << "x_update 4 calculated"
                        << "\n");
    }

    // Store y_update into y
    builder.CreateStore(y_update, y_ptr.value);

    LLVM_DEBUG(dbgs() << "y_update stored"
                      << "\n");

    // Store x_update into x
    builder.CreateStore(x_update, x_ptr.value);

    LLVM_DEBUG(dbgs() << "x_update stored"
                      << "\n");

    /*
      The two parts where we update z and increment the counter are identical for the negative and positive loops and could theoretically be made into a single subroutine.
      However, we want to avoid checking where we are each time, so we duplicate the code.
    */

    {
      // Update z

      // Calculate arctanh_2power[i]
      z_update = builder.CreateGEP(
          getElementTypeFromValuePointer(pointer_to_arctanh_array), pointer_to_arctanh_array,
          {zero_ret_value, i_value}, "atanh_2pwr_i_ptr_loop1");

      LLVM_DEBUG(dbgs() << "z_update: ");
      z_update->print(dbgs(), true);
      LLVM_DEBUG(dbgs() << "\n");

      LLVM_DEBUG(dbgs() << "z_update 1 calculated"
                        << "\n");

      z_update = builder.CreateLoad(getElementTypeFromValuePointer(z_update), z_update, "atanh_2pwr_i_loop1");

      LLVM_DEBUG(dbgs() << "z_update 2 calculated"
                        << "\n");

      // z_update = (update_sign > 0 ? arctanh_2power[i] : -arctanh_2power[i]);
      z_update = builder.CreateSelect(
          update_sign_greater_zero, z_update, builder.CreateSub(zero_ret_value, z_update, "minus_atanh_2pwr_i_loop1"), "arg_update_loop1");

      LLVM_DEBUG(dbgs() << "z_update 3 calculated"
                        << "\n");

      // z_{k+1} = z + z_update
      builder.CreateStore(
          builder.CreateAdd(z_value, z_update, "arg_increment_loop1"), z_ptr.value);

      LLVM_DEBUG(dbgs() << "z_update stored"
                        << "\n");
    }

    // i++
    builder.CreateStore(builder.CreateAdd(i_value,
                                          ConstantInt::get(int_type, 1), "iterator_value_next_loop1"),
                        i_ptr);

    LLVM_DEBUG(dbgs() << "i incremented"
                      << "\n");
    builder.CreateBr(check_loop_negatives);
  }

  // POSITIVE LOOP

  // builder.CreateBr(check_loop_positives);
  builder.SetInsertPoint(check_loop_positives);

  LLVM_DEBUG(dbgs() << "Start positive loop"
                    << "\n");

  // TODO: repeat iterations 4, 13, 40

  i_value = builder.CreateLoad(getElementTypeFromValuePointer(i_ptr), i_ptr, "i_value_loop2");

  // Check whether i < (m+n); if so, go to loop body. Else, go to positive loop.
  Value *iIsLessThanN = builder.CreateICmpSLT(
      i_value,
      ConstantInt::get(int_type, flttofix::cordic_exp_total_iterations), "loop_condition_positives");

  // Execute the loop if i < m+n; else, go to the end of the function.
  builder.CreateCondBr(iIsLessThanN, loop_body_positives,
                       finalize);
  {
    builder.SetInsertPoint(loop_body_positives);

    LLVM_DEBUG(dbgs() << "Start positive loop body"
                      << "\n");


    // Current x y z values
    auto x_value = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_curr_loop2");
    auto y_value = builder.CreateLoad(getElementTypeFromValuePointer(y_ptr.value), y_ptr.value, "y_curr_loop2");
    auto z_value = builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value, "z_curr_loop2");


    // sign = y >= 0 ? 1 : -1;
    Value *update_sign = builder.CreateSelect(
        builder.CreateICmpSGE(y_value, zero_arg_value, "arg_is_negative_loop2"),
        ConstantInt::get(int_type, 1), ConstantInt::get(int_type, -1), "update_sign_loop2");

    // update_sign > 0 ?
    auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_arg_value, "update_sign_greater_zero_loop2");

    // shift_amt = i-m since we do not reset i (again, casted to larger type since otherwise LLVM will complain)
    Value *shift_amt = builder.CreateSub(i_value,
                                         ConstantInt::get(int_type, flttofix::cordic_exp_negative_iterations), "shift_amt_loop2");

    LLVM_DEBUG(dbgs() << "Shift amount set"
                      << "\n");

    {
      // Update y. The update reads x.

      // Calculate x * (2 ^ -shift_amt)
      y_update = builder.CreateAShr(
          x_value, shift_amt, "y_upd_1_loop2");

      LLVM_DEBUG(dbgs() << "y_update 1 calculated"
                        << "\n");

      // Calculate (update_sign > 0 ? -(x * (2 ^ -shift_amt)) : (x * (2 ^ -shift_amt)));
      y_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg_value, y_update, "minus_y_upd_1_loop2"), y_update, "y_upd_2_loop2");

      LLVM_DEBUG(dbgs() << "y_update 2 calculated"
                        << "\n");

      // y_{k+1} = y_k + y_update. Set to temp value since we will need to use y next.
      y_update = builder.CreateAdd(
          y_value, y_update, "y_upd_3_loop2");

      LLVM_DEBUG(dbgs() << "y_update 3 calculated"
                        << "\n");
    }

    {
      // Update x. The update reads y.

      // Calculate y * (2 ^ -shift_amt)
      x_update = builder.CreateAShr(
          y_value, shift_amt, "x_upd_1_loop2");

      LLVM_DEBUG(dbgs() << "x_update 1 calculated"
                        << "\n");

      // Calculate (update_sign > 0 ? -(y * (2 ^ -shift_amt)) : (y * (2 ^ -shift_amt)));
      x_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg_value, x_update, "minus_x_upd_1_loop2"), x_update, "x_upd_2_loop2");

      LLVM_DEBUG(dbgs() << "x_update 2 calculated"
                        << "\n");

      // x_{k+1} = x_k + x_update
      x_update =
          builder.CreateAdd(x_value, x_update, "x_upd_3_loop2");

      LLVM_DEBUG(dbgs() << "x_update 3 calculated"
                        << "\n");
    }

    // Store y_update into y
    builder.CreateStore(y_update, y_ptr.value);

    // Store x_update into x
    builder.CreateStore(x_update, x_ptr.value);

    LLVM_DEBUG(dbgs() << "x and y updated"
                      << "\n");

    /*
      The two parts where we update z and increment the counter are identical for the negative and positive loops and could theoretically be made into a single subroutine.
      However, we want to avoid checking where we are each time, so we duplicate the code.
    */

    {
      // Update z

      // Calculate arctanh_2power[i]
      z_update = builder.CreateGEP(getElementTypeFromValuePointer(pointer_to_arctanh_array), pointer_to_arctanh_array,
                                   {zero_ret_value, i_value}, "atanh_2pwr_i_ptr_loop2");

      LLVM_DEBUG(dbgs() << "z_update: ");
      z_update->print(dbgs(), true);
      LLVM_DEBUG(dbgs() << "\n");

      LLVM_DEBUG(dbgs() << "z_update 1 calculated"
                        << "\n");

      z_update = builder.CreateLoad(getElementTypeFromValuePointer(z_update), z_update, "atanh_2pwr_i_loop2");

      LLVM_DEBUG(dbgs() << "z_update 2 calculated"
                        << "\n");

      // z = z + (update_sign > 0 ? -arctanh_2power[i] : arctanh_2power[i]);
      z_update = builder.CreateSelect(
          update_sign_greater_zero, z_update, builder.CreateSub(zero_arg_value, z_update), "arg_update_loop2");

      LLVM_DEBUG(dbgs() << "z_update 3 calculated"
                        << "\n");

      // z_{k+1} = z_k + z_update
      builder.CreateStore(
          builder.CreateAdd(z_value, z_update, "arg_increment_loop2"), z_ptr.value);

      LLVM_DEBUG(dbgs() << "z_update stored"
                        << "\n");
    }

    // i++
    builder.CreateStore(builder.CreateAdd(i_value,
                                          ConstantInt::get(int_type, 1), "iterator_value_next_loop2"),
                        i_ptr);
    builder.CreateBr(check_loop_positives);

    // Set the insert point to the end of the function, which is after the else.
    builder.SetInsertPoint(finalize);
  }

  LLVM_DEBUG(dbgs() << "End of log routine"
                    << "\n");

  // z_final = 2*z where z =1/2*log10(arg)
  builder.CreateStore(
      builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value), ConstantInt::get(int_type, 1), "value_final_shifted_left"), z_ptr.value);

  if (fxpret.scalarFracBitsAmt() < truefxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value), truefxpret.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), z_ptr.value);
  }

  builder.CreateBr(return_point);
  builder.SetInsertPoint(return_point);

  auto return_value = builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value, "z_value_final");


  LLVM_DEBUG(dbgs() << "return_value after shift: ");
  return_value->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  builder.CreateBr(end);
  builder.SetInsertPoint(end);
  builder.CreateRet(return_value);
  return true;
}

bool createLog2(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  //
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

  auto int_type = fxparg.scalarToLLVMType(cont);

  // ----------------------------------------------------

  // Pointer to the argument
  Value *arg_ptr = builder.CreateAlloca(int_type, nullptr, "arg");
  builder.CreateStore(newfs->getArg(0), arg_ptr);

  LLVM_DEBUG(dbgs() << "arg_ptr: ");
  arg_ptr->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // If the argument is unsigned, make it signed
  if (!fxparg.scalarIsSigned()) {
    LLVM_DEBUG(dbgs() << "Argument is unsigned: shifting it to the right by 1 bit\n");
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), ConstantInt::get(int_type, 1), "unsigned_arg_shifted"), arg_ptr);
    fxparg.scalarFracBitsAmt() = fxparg.scalarFracBitsAmt() - 1;
    fxparg.scalarIsSigned() = true;
  }

  /*
    Define LLVM integer types that will hold our variables.
    The internal variables will have a similar magnitude to the argument, so we can use the same data type with an additional bit for the integer part.
  */
  auto internal_fxpt = flttofix::FixedPointType(true, fxparg.scalarFracBitsAmt() - 1, fxparg.scalarBitsAmt());
  LLVM_DEBUG(dbgs() << "Internal fixed point type: ");
  int_type->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // Generate strings for constants names
  std::string S_ret_point = "." + std::to_string(fxpret.scalarFracBitsAmt());
  std::string S_int_point = "." + std::to_string(internal_fxpt.scalarFracBitsAmt());

  auto truefxpret = fxpret;
  /*
  The largest arcatanh constant we have to use is about 4.6. Internally, we use the return's type; the problem is that if the return's fixed point type has very few integer bits, we may not have enough to represent the various constants.
  Thus, we must make sure that we have at least 4 integer bits +1 for the sign
  */
  if ((fxpret.scalarBitsAmt() - fxpret.scalarFracBitsAmt()) < 5) {
    fxpret = flttofix::FixedPointType(true,
                                      fxpret.scalarBitsAmt() - 5,
                                      fxpret.scalarBitsAmt());
    LLVM_DEBUG(dbgs() << "New fxpret: " << fxpret << "\n");
  }

  // ----------------------------------------------------
  // Basic blocks

  // Block for the initialization of the loop
  BasicBlock *init = BasicBlock::Create(cont, "init", newfs);

  // Blocks where we check loop boundaries
  BasicBlock *check_loop_negatives = BasicBlock::Create(cont, "check_loop_negatives", newfs);
  BasicBlock *check_loop_positives = BasicBlock::Create(cont, "check_loop_positives", newfs);

  // Main loop bodies
  BasicBlock *loop_body_negatives = BasicBlock::Create(cont, "loop_body_negatives", newfs);
  BasicBlock *loop_body_positives = BasicBlock::Create(cont, "loop_body_positives", newfs);

  // In case we did not need to return a special value, we will cast the result to the return type here
  BasicBlock *finalize = BasicBlock::Create(cont, "finalize", newfs);

  // Return block
  BasicBlock *return_point = BasicBlock::Create(cont, "Special", newfs);

  // End block, which returns the result
  BasicBlock *end = BasicBlock::Create(cont, "end", newfs);


  LLVM_DEBUG(dbgs() << "Create init"
                    << "\n");
  builder.CreateBr(init);
  builder.SetInsertPoint(init);

  // ----------------------------------------------------
  // Support variables that we use internally
  // The argument is created above
  TaffoMath::pair_ftp_value<llvm::Value *> x_ptr(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Value *> y_ptr(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Value *> z_ptr(fxpret);
  x_ptr.value = builder.CreateAlloca(int_type, nullptr, "x");
  y_ptr.value = builder.CreateAlloca(int_type, nullptr, "y");
  z_ptr.value = builder.CreateAlloca(int_type, nullptr, "z");

  // Pointer to the current iteration counter
  Value *i_ptr = builder.CreateAlloca(int_type, nullptr, "i_ptr");

  // Pointer to zero in the internal fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_arg(internal_fxpt);
  // Pointer to one in the internal fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> one(internal_fxpt);
  // Pointer to zero in the return fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_ret(fxpret);
  // The arctanh array table
  TaffoMath::pair_ftp_value<llvm::Constant *,
                            TaffoMath::TABLELENGHT>
      arctanh_2power_2;

  // ----------------------------------------------------

  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, internal_fxpt, zero_arg.value, zero_arg.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::one, internal_fxpt, one.value, one.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, fxpret, zero_ret.value, zero_ret.fpt);

  zero_arg.value = TaffoMath::createGlobalConst(
      M, "zero_arg" + S_int_point, zero_arg.fpt.scalarToLLVMType(cont), zero_arg.value,
      dataLayout.getPrefTypeAlignment(zero_arg.fpt.scalarToLLVMType(cont)));

  one.value = TaffoMath::createGlobalConst(
      M, "one" + S_int_point, one.fpt.scalarToLLVMType(cont), one.value,
      dataLayout.getPrefTypeAlignment(one.fpt.scalarToLLVMType(cont)));

  zero_ret.value = TaffoMath::createGlobalConst(
      M, "zero_ret" + S_ret_point, zero_ret.fpt.scalarToLLVMType(cont), zero_ret.value,
      dataLayout.getPrefTypeAlignment(zero_ret.fpt.scalarToLLVMType(cont)));


  // ----------------------------------------------------
  // Create the table for arctanh

  LLVM_DEBUG(dbgs() << "\n===== Create arctanh table ====="
                    << "\n");

  llvm::AllocaInst *pointer_to_arctanh_array = nullptr;

  for (int i = 0; i < TaffoMath::TABLELENGHT; i++) {
    LLVM_DEBUG(dbgs() << "Element " << i << ":\n");
    arctanh_2power_2.fpt.push_back(flttofix::FixedPointType(fxpret));
    Constant *tmp = nullptr;
    auto &current_fpt = arctanh_2power_2.fpt.front();
    TaffoMath::createFixedPointFromConst(
        cont, ref, flttofix::arctanh_2power_2[i], fxpret, tmp, current_fpt);
    arctanh_2power_2.value.push_back(tmp);
    LLVM_DEBUG(dbgs() << "\n");
  }

  auto arctanhArrayType = llvm::ArrayType::get(arctanh_2power_2.value[0]->getType(),
                                               TaffoMath::TABLELENGHT);
  LLVM_DEBUG(dbgs() << "arctanhArrayType: ");
  arctanhArrayType->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  auto arctanhConstArray = llvm::ConstantArray::get(
      arctanhArrayType, llvm::ArrayRef<llvm::Constant *>(arctanh_2power_2.value));

  LLVM_DEBUG(dbgs() << "arctanhConstArray: ");
  arctanhArrayType->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  auto alignement_arctanh =
      dataLayout.getPrefTypeAlignment(arctanh_2power_2.value[0]->getType());
  auto arctan_g =
      TaffoMath::createGlobalConst(M, "arctanh_g." + std::to_string(fxpret.scalarFracBitsAmt()), arctanhArrayType,
                                   arctanhConstArray, alignement_arctanh);

  pointer_to_arctanh_array = builder.CreateAlloca(arctanhArrayType, nullptr, "arctanh_array");
  pointer_to_arctanh_array->setAlignment(llvm::Align(alignement_arctanh));

  builder.CreateMemCpy(
      pointer_to_arctanh_array, llvm::Align(alignement_arctanh), arctan_g, llvm::Align(alignement_arctanh),
      TaffoMath::TABLELENGHT * (int_type->getScalarSizeInBits() >> 3));
  LLVM_DEBUG(dbgs() << "\nAdd to newf arctanh table. Copied " << TaffoMath::TABLELENGHT * (int_type->getScalarSizeInBits() >> 3) << " bytes\n");

  // If the argument is negative, return a special value
  {
    // Shift right arg by 1
    auto arg_value = builder.CreateAShr(
        builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_value"),
        ConstantInt::get(int_type, 1),
        "arg_value_shr_1");
    // Store arg_value in arg_ptr
    builder.CreateStore(arg_value, arg_ptr);

    // Create two blocks: one for the negative case (BTrue) and one for the positive or zero case (BFalse)
    BasicBlock *BTrue = BasicBlock::Create(cont, "Special", newfs);
    BasicBlock *BFalse = BasicBlock::Create(cont, "body", newfs);

    // Create a conditional branch based on the sign check
    Value *check_sign = builder.CreateICmpSLE(
        arg_value,                    // Confronta l'argomento caricato
        ConstantInt::get(int_type, 0) // Confronta con zero per verificare il segno negativo
    );

    builder.CreateCondBr(check_sign, BTrue, BFalse);
    // If negative, handle in BTrue
    builder.SetInsertPoint(BTrue);
    // Calculate the value of the most negative number (-2^(n-1)) for a signed integer
    Value *negative_max = ConstantInt::get(int_type, APInt::getSignedMinValue(truefxpret.scalarBitsAmt()));
    // Store the negative max value in z_ptr.value
    builder.CreateStore(negative_max, z_ptr.value);
    // Jump to the return block (return_point)
    builder.CreateBr(return_point);
    // Handle the non-negative case (BFalse)
    builder.SetInsertPoint(BFalse);
  }

  // calculate log2

  LLVM_DEBUG(dbgs() << "Starting ln routine"
                    << "\n");

  auto zero_arg_value = builder.CreateLoad(getElementTypeFromValuePointer(zero_arg.value), zero_arg.value, "zero_arg");
  LLVM_DEBUG(dbgs() << "zero: ");
  zero_arg_value->print(dbgs(), true);
  auto zero_ret_value = builder.CreateLoad(getElementTypeFromValuePointer(zero_ret.value), zero_ret.value, "zero_ret");
  LLVM_DEBUG(dbgs() << "\n");

  LLVM_DEBUG(dbgs() << "Zero value set"
                    << "\n");

  auto one_value = builder.CreateLoad(getElementTypeFromValuePointer(one.value), one.value, "one");
  auto arg_value = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_value");

  // Initialise x y z
  // x=arg+1
  builder.CreateStore(builder.CreateAdd(arg_value, one_value), x_ptr.value);
  // y=arg-1
  builder.CreateStore(builder.CreateSub(arg_value, one_value), y_ptr.value);
  // z=0
  builder.CreateStore(zero_ret_value, z_ptr.value);

  LLVM_DEBUG(dbgs() << "Initial x y z set"
                    << "\n");

  // Temp values to store updates
  Value *x_update;
  Value *y_update;
  Value *z_update;

  LLVM_DEBUG(dbgs() << "Initial blocks set"
                    << "\n");

  /*
    We need to iterate from -m to 0 and then from 1 to n.

    We first loop on the negative values, then we loop on the positive values.
    The table is the same.
  */

  // NEGATIVE LOOP

  LLVM_DEBUG(dbgs() << "Start negative loop"
                    << "\n");

  builder.CreateStore(zero_ret_value, i_ptr);

  LLVM_DEBUG(dbgs() << "Iterator set"
                    << "\n");

  builder.CreateBr(check_loop_negatives);
  builder.SetInsertPoint(check_loop_negatives);

  auto i_value = builder.CreateLoad(getElementTypeFromValuePointer(i_ptr), i_ptr, "i_value_loop1");

  // Check whether i < m; if so, go to loop body. Else, go to positive loop.
  Value *iIsLessThanM = builder.CreateICmpSLE(
      i_value,
      ConstantInt::get(int_type, flttofix::cordic_exp_negative_iterations), "loop_condition_negatives");

  // Execute the loop if i < m; else, go to the positive loop.
  builder.CreateCondBr(iIsLessThanM, loop_body_negatives,
                       check_loop_positives);
  {
    builder.SetInsertPoint(loop_body_negatives);

    LLVM_DEBUG(dbgs() << "Start negative loop body"
                      << "\n");

    // Current x y z values
    auto x_value = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_curr_loop1");
    auto y_value = builder.CreateLoad(getElementTypeFromValuePointer(y_ptr.value), y_ptr.value, "y_curr_loop1");
    auto z_value = builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value, "z_curr_loop1");

    // sign = y >= 0 ? 1 : -1;
    Value *update_sign = builder.CreateSelect(
        builder.CreateICmpSGE(y_value, zero_arg_value, "y_is_positive_loop2"),
        ConstantInt::get(int_type, 1), ConstantInt::get(int_type, -1), "update_sign_loop2");

    // update_sign > 0 ?
    auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_arg_value, "update_sign_greater_zero_loop2");

    LLVM_DEBUG(dbgs() << "Sign greater than zero set"
                      << "\n");

    /*
      shift_amt = cordic_exp_negative_iterations+2-i (casted to larger type since otherwise LLVM will complain)
      The original loop should compute 2^(-i+2), with i going from -m to 0. However our i starts from 0,
        so we need to compute 2^(m^2-i) instead and then shift right later.
     */
    Value *shift_amt = builder.CreateSub(
        ConstantInt::get(int_type, flttofix::cordic_exp_negative_iterations + 2), i_value, "shift_amt_loop1");

    LLVM_DEBUG(dbgs() << "Shift amount set"
                      << "\n");

    {
      // Update y. The update reads x.

      // Calculate x * (2 ^ -shift_amt)
      y_update = builder.CreateAShr(
          x_value, shift_amt, "y_upd_1_loop1");

      LLVM_DEBUG(dbgs() << "y_update 1 calculated"
                        << "\n");

      // Calculate x - x * (2 ^ -shift_amt)
      y_update = builder.CreateSub(
          x_value, y_update, "y_upd_2_loop1");

      LLVM_DEBUG(dbgs() << "y_update 2 calculated"
                        << "\n");

      // Calculate (update_sign > 0 ? -(x - x * (2 ^ -shift_amt)) : (x - x * (2 ^ -shift_amt)));
      y_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg_value, y_update, "minus_y_upd_2_loop1"), y_update, "y_upd_3_loop1");

      LLVM_DEBUG(dbgs() << "y_update 3 calculated"
                        << "\n");

      // y_{k+1} = y_k + y_update. Set to temp value since we will need to use y next.
      y_update = builder.CreateAdd(
          y_value, y_update, "y_upd_4_loop1");

      LLVM_DEBUG(dbgs() << "y_update 4 calculated"
                        << "\n");
    }

    {
      // Update x. The update reads y.

      // Calculate y * (2 ^ -shift_amt)
      x_update = builder.CreateAShr(
          y_value, shift_amt, "x_upd_1_loop1");

      LLVM_DEBUG(dbgs() << "x_update 1 calculated"
                        << "\n");

      // Calculate y - y * (2 ^ -shift_amt)
      x_update = builder.CreateSub(
          y_value, x_update, "x_upd_2_loop1");

      LLVM_DEBUG(dbgs() << "x_update 2 calculated"
                        << "\n");

      // Calculate (update_sign > 0 ? -(y - y * (2 ^ -shift_amt)) : (y - y * (2 ^ -shift_amt)));
      x_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg_value, x_update, "minus_x_upd_2_loop1"), x_update, "x_upd_3_loop1");

      LLVM_DEBUG(dbgs() << "x_update 3 calculated"
                        << "\n");

      // x_{k+1} = x_k + x_update
      x_update =
          builder.CreateAdd(x_value, x_update, "x_upd_4_loop1");

      LLVM_DEBUG(dbgs() << "x_update 4 calculated"
                        << "\n");
    }

    // Store y_update into y
    builder.CreateStore(y_update, y_ptr.value);

    LLVM_DEBUG(dbgs() << "y_update stored"
                      << "\n");

    // Store x_update into x
    builder.CreateStore(x_update, x_ptr.value);

    LLVM_DEBUG(dbgs() << "x_update stored"
                      << "\n");

    /*
      The two parts where we update z and increment the counter are identical for the negative and positive loops and could theoretically be made into a single subroutine.
      However, we want to avoid checking where we are each time, so we duplicate the code.
    */

    {
      // Update z

      // Calculate arctanh_2power[i]
      z_update = builder.CreateGEP(
          getElementTypeFromValuePointer(pointer_to_arctanh_array), pointer_to_arctanh_array,
          {zero_ret_value, i_value}, "atanh_2pwr_i_ptr_loop1");

      LLVM_DEBUG(dbgs() << "z_update: ");
      z_update->print(dbgs(), true);
      LLVM_DEBUG(dbgs() << "\n");

      LLVM_DEBUG(dbgs() << "z_update 1 calculated"
                        << "\n");

      z_update = builder.CreateLoad(getElementTypeFromValuePointer(z_update), z_update, "atanh_2pwr_i_loop1");

      LLVM_DEBUG(dbgs() << "z_update 2 calculated"
                        << "\n");

      // z_update = (update_sign > 0 ? arctanh_2power[i] : -arctanh_2power[i]);
      z_update = builder.CreateSelect(
          update_sign_greater_zero, z_update, builder.CreateSub(zero_ret_value, z_update, "minus_atanh_2pwr_i_loop1"), "arg_update_loop1");

      LLVM_DEBUG(dbgs() << "z_update 3 calculated"
                        << "\n");

      // z_{k+1} = z + z_update
      builder.CreateStore(
          builder.CreateAdd(z_value, z_update, "arg_increment_loop1"), z_ptr.value);

      LLVM_DEBUG(dbgs() << "z_update stored"
                        << "\n");
    }

    // i++
    builder.CreateStore(builder.CreateAdd(i_value,
                                          ConstantInt::get(int_type, 1), "iterator_value_next_loop1"),
                        i_ptr);

    LLVM_DEBUG(dbgs() << "i incremented"
                      << "\n");
    builder.CreateBr(check_loop_negatives);
  }

  // POSITIVE LOOP

  // builder.CreateBr(check_loop_positives);
  builder.SetInsertPoint(check_loop_positives);

  LLVM_DEBUG(dbgs() << "Start positive loop"
                    << "\n");

  // TODO: repeat iterations 4, 13, 40

  i_value = builder.CreateLoad(getElementTypeFromValuePointer(i_ptr), i_ptr, "i_value_loop2");

  // Check whether i < (m+n); if so, go to loop body. Else, go to positive loop.
  Value *iIsLessThanN = builder.CreateICmpSLT(
      i_value,
      ConstantInt::get(int_type, flttofix::cordic_exp_total_iterations), "loop_condition_positives");

  // Execute the loop if i < m+n; else, go to the end of the function.
  builder.CreateCondBr(iIsLessThanN, loop_body_positives,
                       finalize);
  {
    builder.SetInsertPoint(loop_body_positives);

    LLVM_DEBUG(dbgs() << "Start positive loop body"
                      << "\n");


    // Current x y z values
    auto x_value = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_curr_loop2");
    auto y_value = builder.CreateLoad(getElementTypeFromValuePointer(y_ptr.value), y_ptr.value, "y_curr_loop2");
    auto z_value = builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value, "z_curr_loop2");


    // sign = y >= 0 ? 1 : -1;
    Value *update_sign = builder.CreateSelect(
        builder.CreateICmpSGE(y_value, zero_arg_value, "arg_is_negative_loop2"),
        ConstantInt::get(int_type, 1), ConstantInt::get(int_type, -1), "update_sign_loop2");

    // update_sign > 0 ?
    auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_arg_value, "update_sign_greater_zero_loop2");

    // shift_amt = i-m since we do not reset i (again, casted to larger type since otherwise LLVM will complain)
    Value *shift_amt = builder.CreateSub(i_value,
                                         ConstantInt::get(int_type, flttofix::cordic_exp_negative_iterations), "shift_amt_loop2");

    LLVM_DEBUG(dbgs() << "Shift amount set"
                      << "\n");

    {
      // Update y. The update reads x.

      // Calculate x * (2 ^ -shift_amt)
      y_update = builder.CreateAShr(
          x_value, shift_amt, "y_upd_1_loop2");

      LLVM_DEBUG(dbgs() << "y_update 1 calculated"
                        << "\n");

      // Calculate (update_sign > 0 ? -(x * (2 ^ -shift_amt)) : (x * (2 ^ -shift_amt)));
      y_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg_value, y_update, "minus_y_upd_1_loop2"), y_update, "y_upd_2_loop2");

      LLVM_DEBUG(dbgs() << "y_update 2 calculated"
                        << "\n");

      // y_{k+1} = y_k + y_update. Set to temp value since we will need to use y next.
      y_update = builder.CreateAdd(
          y_value, y_update, "y_upd_3_loop2");

      LLVM_DEBUG(dbgs() << "y_update 3 calculated"
                        << "\n");
    }

    {
      // Update x. The update reads y.

      // Calculate y * (2 ^ -shift_amt)
      x_update = builder.CreateAShr(
          y_value, shift_amt, "x_upd_1_loop2");

      LLVM_DEBUG(dbgs() << "x_update 1 calculated"
                        << "\n");

      // Calculate (update_sign > 0 ? -(y * (2 ^ -shift_amt)) : (y * (2 ^ -shift_amt)));
      x_update = builder.CreateSelect(
          update_sign_greater_zero, builder.CreateSub(zero_arg_value, x_update, "minus_x_upd_1_loop2"), x_update, "x_upd_2_loop2");

      LLVM_DEBUG(dbgs() << "x_update 2 calculated"
                        << "\n");

      // x_{k+1} = x_k + x_update
      x_update =
          builder.CreateAdd(x_value, x_update, "x_upd_3_loop2");

      LLVM_DEBUG(dbgs() << "x_update 3 calculated"
                        << "\n");
    }

    // Store y_update into y
    builder.CreateStore(y_update, y_ptr.value);

    // Store x_update into x
    builder.CreateStore(x_update, x_ptr.value);

    LLVM_DEBUG(dbgs() << "x and y updated"
                      << "\n");

    /*
      The two parts where we update z and increment the counter are identical for the negative and positive loops and could theoretically be made into a single subroutine.
      However, we want to avoid checking where we are each time, so we duplicate the code.
    */

    {
      // Update z

      // Calculate arctanh_2power[i]
      z_update = builder.CreateGEP(getElementTypeFromValuePointer(pointer_to_arctanh_array), pointer_to_arctanh_array,
                                   {zero_ret_value, i_value}, "atanh_2pwr_i_ptr_loop2");

      LLVM_DEBUG(dbgs() << "z_update: ");
      z_update->print(dbgs(), true);
      LLVM_DEBUG(dbgs() << "\n");

      LLVM_DEBUG(dbgs() << "z_update 1 calculated"
                        << "\n");

      z_update = builder.CreateLoad(getElementTypeFromValuePointer(z_update), z_update, "atanh_2pwr_i_loop2");

      LLVM_DEBUG(dbgs() << "z_update 2 calculated"
                        << "\n");

      // z = z + (update_sign > 0 ? -arctanh_2power[i] : arctanh_2power[i]);
      z_update = builder.CreateSelect(
          update_sign_greater_zero, z_update, builder.CreateSub(zero_arg_value, z_update), "arg_update_loop2");

      LLVM_DEBUG(dbgs() << "z_update 3 calculated"
                        << "\n");

      // z_{k+1} = z_k + z_update
      builder.CreateStore(
          builder.CreateAdd(z_value, z_update, "arg_increment_loop2"), z_ptr.value);

      LLVM_DEBUG(dbgs() << "z_update stored"
                        << "\n");
    }

    // i++
    builder.CreateStore(builder.CreateAdd(i_value,
                                          ConstantInt::get(int_type, 1), "iterator_value_next_loop2"),
                        i_ptr);
    builder.CreateBr(check_loop_positives);

    // Set the insert point to the end of the function, which is after the else.
    builder.SetInsertPoint(finalize);
  }

  LLVM_DEBUG(dbgs() << "End of log routine"
                    << "\n");

  // z_final = 2*z where z =1/2*log2(arg)
  builder.CreateStore(
      builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value), ConstantInt::get(int_type, 1), "value_final_shifted_left"), z_ptr.value);

  if (fxpret.scalarFracBitsAmt() < truefxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value), truefxpret.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), z_ptr.value);
  }

  builder.CreateBr(return_point);
  builder.SetInsertPoint(return_point);

  auto return_value = builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value, "z_value_final");


  LLVM_DEBUG(dbgs() << "return_value after shift: ");
  return_value->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  builder.CreateBr(end);
  builder.SetInsertPoint(end);
  builder.CreateRet(return_value);
  return true;
}

} // namespace flttofix
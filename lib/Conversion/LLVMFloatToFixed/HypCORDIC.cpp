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
#include "llvm/Support/raw_ostream.h"
#include <string>
#include <vector>

#define DEBUG_TYPE "taffo-conversion"

bool createExp(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
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


  /*if ((fxpret.scalarBitsAmt() - fxpret.scalarFracBitsAmt()) < 5) {
    fxpret = flttofix::FixedPointType(true,
                                      fxpret.scalarBitsAmt() - 5,
                                      fxpret.scalarBitsAmt());
    LLVM_DEBUG(dbgs() << "New fxpret: " << fxpret << "\n");
  }*/

  LLVM_DEBUG(dbgs() << "fxpret: " << fxpret.scalarBitsAmt() << " frac part: " << fxpret.scalarFracBitsAmt() << " difference: " << fxpret.scalarBitsAmt() - fxpret.scalarFracBitsAmt() << "\n");

  // FIXME FIXME

  /*
    In case the argument is positive we can use the same data type for x and y, as they will end up at a similar magnitude.

    In case the argument is negative, x and y will still end up at a similar magnitude, but with opposite signs.
    This means that we subtract one from the other and the return value will be close to 0 and we cannot rely on the estimated range for the output.

    The solution for now is to just use an intermediate fixed point type with a larger number of bits: we use 64 bits in total. We estimated that x and y may get up to about 20'000 for an exponent of -15; this means that they will fit into a data type with 16 bits in the integer part (i.e. 15 bits for the integer part and 1 bit for the sign).
  */
  auto internal_fxpt = flttofix::FixedPointType(true, TaffoMath::cordic_exp_internal_width_fractional, TaffoMath::cordic_exp_internal_width);

  auto int_type_wide = internal_fxpt.scalarToLLVMType(cont);
  LLVM_DEBUG(dbgs() << "Internal fixed point type: ");
  int_type_wide->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  auto int_type_narrow = fxpret.scalarToLLVMType(cont);
  LLVM_DEBUG(dbgs() << "Return fixed point type: ");
  int_type_narrow->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // TaffoMath::pair_ftp_value<llvm::Value *> arg(internal_fxpt);
  // arg.value = newfs->arg_begin();
  //  auto truefxpret = fxpret;

  // create local variable
  // TODO: Check bit width for this
  TaffoMath::pair_ftp_value<llvm::Value *> x_ptr(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Value *> y_ptr(internal_fxpt);
  x_ptr.value = builder.CreateAlloca(int_type_wide, nullptr, "x");
  y_ptr.value = builder.CreateAlloca(int_type_wide, nullptr, "y");

  // We need to cast the argument to the internal fixed point type
  // Allocate memory for arg_ptr
  Value *arg_ptr = builder.CreateAlloca(int_type_narrow, nullptr, "arg");
  // Sign-extend
  // Value *arg_value_wide = builder.CreateSExt(newfs->getArg(0), int_type_wide, "sign_extended_arg");

  // LLVM_DEBUG(dbgs() << "arg_value_wide: ");
  // arg_value_wide->print(dbgs(), true);
  // LLVM_DEBUG(dbgs() << "\n");

  // Store the casted value in arg_ptr
  // builder.CreateStore(arg_value_wide, arg_ptr);
  // Shift the argument to the left to realign the fractional part
  // arg_value_wide = builder.CreateShl(arg_value_wide, internal_fxpt.scalarFracBitsAmt() - fxparg.scalarFracBitsAmt(), "arg_value_wide");
  // Store the shifted value in arg_ptr
  builder.CreateStore(newfs->getArg(0), arg_ptr);

  // LLVM_DEBUG(dbgs() << "Arg was casted. arg_value_wide: ");
  // arg_value_wide->print(dbgs(), true);
  // LLVM_DEBUG(dbgs() << "\n");

  LLVM_DEBUG(dbgs() << "arg_ptr: ");
  arg_ptr->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  Value *i_ptr = builder.CreateAlloca(int_type_narrow, nullptr, "i_ptr");

  TaffoMath::pair_ftp_value<llvm::Constant *> kopp(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_ptr_wide(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_ptr_narrow(fxpret);
  TaffoMath::pair_ftp_value<llvm::Constant *> An_ptr(internal_fxpt);

  LLVM_DEBUG(dbgs() << "Initialising variables. 1/An_ptr=" << TaffoMath::compute_An_inv(-TaffoMath::cordic_exp_negative_iterations, TaffoMath::cordic_exp_positive_iterations)
                    << "\n");

  bool kopp_created = TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::Kopp, internal_fxpt, kopp.value, kopp.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, internal_fxpt, zero_ptr_wide.value, zero_ptr_wide.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, fxpret, zero_ptr_narrow.value, zero_ptr_narrow.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::compute_An_inv(-TaffoMath::cordic_exp_negative_iterations, TaffoMath::cordic_exp_positive_iterations), internal_fxpt, An_ptr.value, An_ptr.fpt);

  std::string S_ret_point = "." + std::to_string(fxpret.scalarFracBitsAmt());
  std::string S_int_point = "." + std::to_string(internal_fxpt.scalarFracBitsAmt());

  if (kopp_created)
    kopp.value = TaffoMath::createGlobalConst(
        M, "kopp" + S_int_point, kopp.fpt.scalarToLLVMType(cont), kopp.value,
        dataLayout.getPrefTypeAlignment(kopp.fpt.scalarToLLVMType(cont)));

  zero_ptr_wide.value = TaffoMath::createGlobalConst(
      M, "zero_ptr_wide" + S_int_point, zero_ptr_wide.fpt.scalarToLLVMType(cont), zero_ptr_wide.value,
      dataLayout.getPrefTypeAlignment(zero_ptr_wide.fpt.scalarToLLVMType(cont)));

  zero_ptr_narrow.value = TaffoMath::createGlobalConst(
      M, "zero_ptr_narrow" + S_ret_point, zero_ptr_narrow.fpt.scalarToLLVMType(cont), zero_ptr_narrow.value,
      dataLayout.getPrefTypeAlignment(zero_ptr_narrow.fpt.scalarToLLVMType(cont)));

  An_ptr.value = TaffoMath::createGlobalConst(
      M, "An_ptr" + S_int_point, An_ptr.fpt.scalarToLLVMType(cont), An_ptr.value,
      dataLayout.getPrefTypeAlignment(An_ptr.fpt.scalarToLLVMType(cont)));

  /** create arctanh table
   **/
  LLVM_DEBUG(dbgs() << "===== Create arctanh table ====="
                    << "\n");
  TaffoMath::pair_ftp_value<llvm::Constant *,
                            TaffoMath::TABLELENGHT>
      arctanh_2power;
  llvm::AllocaInst *pointer_to_arctanh_array = nullptr;

  if (!MathZFlag) {
    for (int i = 0; i < TaffoMath::TABLELENGHT; i++) {
      LLVM_DEBUG(dbgs() << "Element " << i << ":\n");
      arctanh_2power.fpt.push_back(flttofix::FixedPointType(fxparg));
      Constant *tmp = nullptr;
      auto &current_fpt = arctanh_2power.fpt.front();
      TaffoMath::createFixedPointFromConst(
          cont, ref, TaffoMath::arctanh_2power[i], fxparg, tmp, current_fpt);
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
        TaffoMath::createGlobalConst(M, "arctanh_g." + std::to_string(fxparg.scalarFracBitsAmt()), arctanhArrayType,
                                     arctanhConstArray, alignement_arctanh);

    pointer_to_arctanh_array = builder.CreateAlloca(arctanhArrayType, nullptr, "arctanh_array");
    pointer_to_arctanh_array->setAlignment(llvm::Align(alignement_arctanh));

    builder.CreateMemCpy(
        pointer_to_arctanh_array, llvm::Align(alignement_arctanh), arctan_g, llvm::Align(alignement_arctanh),
        TaffoMath::TABLELENGHT * (int_type_narrow->getScalarSizeInBits() >> 3));
    LLVM_DEBUG(dbgs() << "\nAdd to newf arctanh table. Copied " << TaffoMath::TABLELENGHT * (int_type_narrow->getScalarSizeInBits() >> 3) << " bytes\n");
  }

  BasicBlock *init = BasicBlock::Create(cont, "init", newfs);
  builder.CreateBr(init);
  builder.SetInsertPoint(init);
  LLVM_DEBUG(dbgs() << "Create init"
                    << "\n");
  // arg.value = arg_ptr;
  BasicBlock *finalize = BasicBlock::Create(cont, "finalize", newfs);
  // handle unsigned arg
  if (!fxparg.scalarIsSigned()) {
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), ConstantInt::get(int_type_wide, 1)), arg_ptr);
    fxparg.scalarFracBitsAmt() = fxparg.scalarFracBitsAmt() - 1;
    fxparg.scalarIsSigned() = true;
  }

  LLVM_DEBUG(dbgs() << "fxparg: " << fxparg.scalarBitsAmt() << " frac part: " << fxparg.scalarFracBitsAmt() << " difference: " << fxparg.scalarBitsAmt() - fxparg.scalarFracBitsAmt() << "\n");

  // TODO: Handle sinh, cosh, etc.

  // TODO: Handle special cases

  // calculate exp
  if (!MathZFlag) {
    LLVM_DEBUG(dbgs() << "Starting exp routine"
                      << "\n");
    // builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), internal_fxpt.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), arg_ptr);

    auto zero_value_wide = builder.CreateLoad(getElementTypeFromValuePointer(zero_ptr_wide.value), zero_ptr_wide.value, "zero_wide");
    LLVM_DEBUG(dbgs() << "zero_value_wide: ");
    zero_value_wide->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto zero_value_narrow = builder.CreateLoad(getElementTypeFromValuePointer(zero_ptr_narrow.value), zero_ptr_narrow.value, "zero_narrow");
    LLVM_DEBUG(dbgs() << "zero_value_narrow: ");
    zero_value_narrow->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    LLVM_DEBUG(dbgs() << "Zero value set"
                      << "\n");

    // TODO: Add constant
    auto An_value = builder.CreateLoad(getElementTypeFromValuePointer(An_ptr.value), An_ptr.value, "An_value");
    // Initialise x and y to the initial constant (which depends on the amount of iterations we do)
    // x=An
    builder.CreateStore(An_value, x_ptr.value);
    // y=An
    builder.CreateStore(An_value, y_ptr.value);

    LLVM_DEBUG(dbgs() << "Initial x and y set"
                      << "\n");

    // Blocks where we check loop boundaries
    BasicBlock *check_loop_negatives = BasicBlock::Create(cont, "check_loop_negatives", newfs);
    BasicBlock *check_loop_positives = BasicBlock::Create(cont, "check_loop_positives", newfs);

    // Main loop bodies
    BasicBlock *loop_body_negatives = BasicBlock::Create(cont, "loop_body_negatives", newfs);
    BasicBlock *loop_body_positives = BasicBlock::Create(cont, "loop_body_positives", newfs);

    // Temp values to store updates
    Value *x_update;
    Value *y_update;

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

    builder.CreateStore(zero_value_narrow, i_ptr);

    LLVM_DEBUG(dbgs() << "Iterator set"
                      << "\n");

    builder.CreateBr(check_loop_negatives);
    builder.SetInsertPoint(check_loop_negatives);

    auto i_value = builder.CreateLoad(getElementTypeFromValuePointer(i_ptr), i_ptr, "i_value_loop1");
    auto i_value_wide = builder.CreateZExt(
        i_value, int_type_wide, "i_value_wide_loop1");

    // Check whether i < m; if so, go to loop body. Else, go to positive loop.
    Value *iIsLessThanM = builder.CreateICmpSLE(
        i_value,
        ConstantInt::get(int_type_narrow, TaffoMath::cordic_exp_negative_iterations), "loop_condition_negatives");

    // Execute the loop if i < m; else, go to the positive loop.
    builder.CreateCondBr(iIsLessThanM, loop_body_negatives,
                         check_loop_positives);
    {
      builder.SetInsertPoint(loop_body_negatives);

      LLVM_DEBUG(dbgs() << "Start negative loop body"
                        << "\n");

      // Current argument value
      auto arg_value_narrow = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "curr_arg_val_narrow_loop1");
      Value *arg_value_wide = builder.CreateShl(builder.CreateSExt(arg_value_narrow, int_type_wide, "sign_extended_arg_loop1"), internal_fxpt.scalarFracBitsAmt() - fxparg.scalarFracBitsAmt(), "curr_arg_val_wide_loop1");

      // Current x and y values
      auto x_value = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_curr_loop1");
      auto y_value = builder.CreateLoad(getElementTypeFromValuePointer(y_ptr.value), y_ptr.value, "y_curr_loop1");

      // sign = arg >= 0 ? 1 : -1;
      Value *update_sign = builder.CreateSelect(
          builder.CreateICmpSGE(arg_value_wide, zero_value_wide, "arg_greater_zero_loop1"),
          ConstantInt::get(int_type_wide, 1), ConstantInt::get(int_type_wide, -1), "update_sign_loop1");
      // update_sign > 0 ?
      auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_value_wide, "update_sign_greater_zero_loop1");

      // sign = arg >= 0 ? 1 : -1;
      Value *update_sign_narrow = builder.CreateSelect(
          builder.CreateICmpSGE(arg_value_narrow, zero_value_narrow, "arg_greater_zero_narrow_loop1"),
          ConstantInt::get(int_type_narrow, 1), ConstantInt::get(int_type_narrow, -1), "update_sign_narrow_loop1");
      // update_sign > 0 ?
      auto update_sign_greater_zero_narrow = builder.CreateICmpSGT(update_sign_narrow, zero_value_narrow, "update_sign_greater_zero_narrow_loop1");

      LLVM_DEBUG(dbgs() << "Sign greater than zero set"
                        << "\n");

      /*
        shift_amt = cordic_exp_negative_iterations+2-i (casted to larger type since otherwise LLVM will complain)
        The original loop should compute 2^(-i+2), with i going from -m to 0. However our i starts from 0,
          so we need to compute 2^(m^2-i) instead and then shift right later.
       */
      Value *shift_amt = builder.CreateSub(
          ConstantInt::get(int_type_wide, TaffoMath::cordic_exp_negative_iterations + 2), i_value_wide, "shift_amt_loop1");

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
            update_sign_greater_zero, builder.CreateSub(zero_value_wide, y_update, "minus_y_upd_2_loop1"), y_update, "y_upd_3_loop1");

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
            update_sign_greater_zero, builder.CreateSub(zero_value_wide, x_update, "minus_x_upd_2_loop1"), x_update, "x_upd_3_loop1");

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
        // Update z (= arg)

        // Calculate arctanh_2power[i]
        Value *z_update = builder.CreateGEP(
            getElementTypeFromValuePointer(pointer_to_arctanh_array), pointer_to_arctanh_array,
            {zero_value_narrow, i_value}, "atanh_2pwr_i_ptr_loop1");

        LLVM_DEBUG(dbgs() << "z_update: ");
        z_update->print(dbgs(), true);
        LLVM_DEBUG(dbgs() << "\n");

        LLVM_DEBUG(dbgs() << "z_update 1 calculated"
                          << "\n");

        z_update = builder.CreateLoad(getElementTypeFromValuePointer(z_update), z_update, "atanh_2pwr_i_loop1");

        LLVM_DEBUG(dbgs() << "z_update 2 calculated"
                          << "\n");

        // arg = (update_sign > 0 ? -arctanh_2power[i] : arctanh_2power[i]);
        z_update = builder.CreateSelect(
            update_sign_greater_zero_narrow, builder.CreateSub(zero_value_narrow, z_update, "minus_atanh_2pwr_i_loop1"), z_update, "arg_update_loop1");

        LLVM_DEBUG(dbgs() << "z_update 3 calculated"
                          << "\n");

        // arg_{k+1} = arg_k + z_update
        builder.CreateStore(
            builder.CreateAdd(z_update, arg_value_narrow, "arg_increment_loop1"), arg_ptr);

        LLVM_DEBUG(dbgs() << "z_update stored"
                          << "\n");
      }

      // i++
      builder.CreateStore(builder.CreateAdd(i_value,
                                            ConstantInt::get(int_type_narrow, 1), "iterator_value_next_loop1"),
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
    i_value_wide = builder.CreateZExt(
        i_value, int_type_wide, "i_value_wide_loop2");

    // Check whether i < (m+n); if so, go to loop body. Else, go to positive loop.
    Value *iIsLessThanN = builder.CreateICmpSLT(
        i_value,
        ConstantInt::get(int_type_narrow, TaffoMath::cordic_exp_total_iterations), "loop_condition_positives");

    // Execute the loop if i < m+n; else, go to the end of the function.
    builder.CreateCondBr(iIsLessThanN, loop_body_positives,
                         finalize);
    {
      builder.SetInsertPoint(loop_body_positives);

      LLVM_DEBUG(dbgs() << "Start positive loop body"
                        << "\n");

      // Current argument value
      auto arg_value_narrow = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "curr_arg_val_narrow_loop2");
      Value *arg_value_wide = builder.CreateShl(builder.CreateSExt(arg_value_narrow, int_type_wide, "sign_extended_arg_loop2"), internal_fxpt.scalarFracBitsAmt() - fxparg.scalarFracBitsAmt(), "curr_arg_val_wide_loop2");
      // Current x and y values
      auto x_value = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_curr_loop2");
      auto y_value = builder.CreateLoad(getElementTypeFromValuePointer(y_ptr.value), y_ptr.value, "y_curr_loop2");


      // sign = arg >= 0 ? 1 : -1;
      Value *update_sign = builder.CreateSelect(
          builder.CreateICmpSGE(arg_value_wide, zero_value_wide, "arg_greater_zero_loop2"),
          ConstantInt::get(int_type_wide, 1), ConstantInt::get(int_type_wide, -1), "update_sign_loop2");
      // update_sign > 0 ?
      auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_value_wide, "update_sign_greater_zero_loop2");

      // sign = arg >= 0 ? 1 : -1;
      Value *update_sign_narrow = builder.CreateSelect(
          builder.CreateICmpSGE(arg_value_narrow, zero_value_narrow, "arg_greater_zero_narrow_loop2"),
          ConstantInt::get(int_type_narrow, 1), ConstantInt::get(int_type_narrow, -1), "update_sign_narrow_loop2");
      // update_sign > 0 ?
      auto update_sign_greater_zero_narrow = builder.CreateICmpSGT(update_sign_narrow, zero_value_narrow, "update_sign_greater_zero_narrow_loop2");

      // shift_amt = i-m since we do not reset i (again, casted to larger type since otherwise LLVM will complain)
      Value *shift_amt = builder.CreateSub(i_value_wide,
                                           ConstantInt::get(int_type_wide, TaffoMath::cordic_exp_negative_iterations), "shift_amt_loop2");

      LLVM_DEBUG(dbgs() << "Shift amount set"
                        << "\n");

      {
        // Update y. The update reads x.

        // Calculate x * (2 ^ -shift_amt)
        y_update = builder.CreateAShr(
            x_value, shift_amt, "y_upd_1_loop2");

        LLVM_DEBUG(dbgs() << "y_update 1 calculated"
                          << "\n");

        // Calculate (update_sign > 0 ? -(x - x * (2 ^ -shift_amt)) : (x - x * (2 ^ -shift_amt)));
        y_update = builder.CreateSelect(
            update_sign_greater_zero, builder.CreateSub(zero_value_wide, y_update, "minus_y_upd_1_loop2"), y_update, "y_upd_2_loop2");

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
            update_sign_greater_zero, builder.CreateSub(zero_value_wide, x_update, "minus_x_upd_1_loop2"), x_update, "x_upd_2_loop2");

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
        // Update z (= arg)

        // Calculate arctanh_2power[i]
        Value *z_update = builder.CreateGEP(getElementTypeFromValuePointer(pointer_to_arctanh_array), pointer_to_arctanh_array,
                                            {zero_value_narrow, i_value}, "atanh_2pwr_i_ptr_loop2");

        LLVM_DEBUG(dbgs() << "z_update: ");
        z_update->print(dbgs(), true);
        LLVM_DEBUG(dbgs() << "\n");

        LLVM_DEBUG(dbgs() << "z_update 1 calculated"
                          << "\n");

        z_update = builder.CreateLoad(getElementTypeFromValuePointer(z_update), z_update, "atanh_2pwr_i_loop2");

        LLVM_DEBUG(dbgs() << "z_update 2 calculated"
                          << "\n");

        // arg = arg + (update_sign > 0 ? -arctanh_2power[i] : arctanh_2power[i]);
        z_update = builder.CreateSelect(
            update_sign_greater_zero_narrow, builder.CreateSub(zero_value_narrow, z_update, "minus_atanh_2pwr_i_loop2"), z_update, "arg_update_loop2");

        LLVM_DEBUG(dbgs() << "z_update 3 calculated"
                          << "\n");

        // arg_{k+1} = arg_k + z_update
        builder.CreateStore(
            builder.CreateAdd(z_update, arg_value_narrow, "arg_increment_loop2"), arg_ptr);

        LLVM_DEBUG(dbgs() << "z_update stored"
                          << "\n");
      }

      // i++
      builder.CreateStore(builder.CreateAdd(i_value,
                                            ConstantInt::get(int_type_narrow, 1), "iterator_value_next_loop2"),
                          i_ptr);
      builder.CreateBr(check_loop_positives);

      // Set the insert point to the end of the function, which is after the else.
      builder.SetInsertPoint(finalize);
    }
  } else {
    // TODO
  }

  LLVM_DEBUG(dbgs() << "End of exp routine"
                    << "\n");

  {
    // TODO: handle other functions
  }

  /*if (internal_fxpt.scalarFracBitsAmt() > truefxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), internal_fxpt.scalarFracBitsAmt() - truefxpret.scalarFracBitsAmt()), arg_ptr);
  } else if (internal_fxpt.scalarFracBitsAmt() < truefxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), truefxpret.scalarFracBitsAmt() - internal_fxpt.scalarFracBitsAmt()), arg_ptr);
  }*/

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
  Value *return_value = builder.CreateAShr(ret, ConstantInt::get(int_type_wide, internal_fxpt.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), "arg_value_final_shifted");

  LLVM_DEBUG(dbgs() << "return_value after shift: ");
  return_value->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // Allocate return value

  return_value = builder.CreateTrunc(return_value, int_type_narrow, "output");
  LLVM_DEBUG(dbgs() << "return_value: ");
  return_value->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  BasicBlock *end = BasicBlock::Create(cont, "end", newfs);
  builder.CreateBr(end);
  builder.SetInsertPoint(end);
  builder.CreateRet(return_value);
  return true;
}
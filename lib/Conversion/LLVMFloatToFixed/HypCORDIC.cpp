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
  // auto internal_fxpt = flttofix::FixedPointType(true, fxpret.scalarBitsAmt() - 2, fxpret.scalarBitsAmt());
  /*
    In case the argument is positive we can use the same data type for x and y, as they will end up at a similar magnitude.

    In case the argument is negative, x and y will still end up at a similar magnitude, but with opposite signs.
    This means that we subtract one from the other and the return value will be close to 0 and we cannot rely on the estimated range for the output.

    The solution for now is to just use an intermediate fixed point type with a larger number of bits: we use 64 bits in total. We estimated that x and y may get up to about 20'000 for an exponent of -15; this means that they will fit into a data type with 16 bits in the integer part (i.e. 15 bits for the integer part and 1 bit for the sign).
  */
  auto internal_fxpt = flttofix::FixedPointType(true, TaffoMath::cordic_exp_internal_width_fractional, TaffoMath::cordic_exp_internal_width);

  auto int_type = internal_fxpt.scalarToLLVMType(cont);
  LLVM_DEBUG(dbgs() << "Internal fixed point type: ");
  int_type->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  auto int_type_small = fxpret.scalarToLLVMType(cont);
  LLVM_DEBUG(dbgs() << "Return fixed point type: ");
  int_type_small->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  TaffoMath::pair_ftp_value<llvm::Value *> arg(internal_fxpt);
  arg.value = newfs->arg_begin();
  auto truefxpret = fxpret;

  // create local variable
  // TODO: Check bit width for this
  TaffoMath::pair_ftp_value<llvm::Value *> x_value(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Value *> y_value(internal_fxpt);
  x_value.value = builder.CreateAlloca(int_type, nullptr, "x");
  y_value.value = builder.CreateAlloca(int_type, nullptr, "y");

  // We need to cast the argument to the internal fixed point type
  // Allocate memory for arg_value
  Value *arg_value = builder.CreateAlloca(int_type, nullptr, "arg");
  // Sign-extend
  Value *casted_arg = builder.CreateSExt(newfs->getArg(0), int_type, "sign_extended_arg");

  LLVM_DEBUG(dbgs() << "casted_arg: ");
  casted_arg->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // Store the casted value in arg_value
  builder.CreateStore(casted_arg, arg_value);
  // Shift the argument to the left to realign the fractional part
  casted_arg = builder.CreateShl(casted_arg, internal_fxpt.scalarFracBitsAmt() - fxparg.scalarFracBitsAmt(), "casted_arg");
  // Store the shifted value in arg_value
  builder.CreateStore(casted_arg, arg_value);

  LLVM_DEBUG(dbgs() << "Arg was casted. casted_arg: ");
  casted_arg->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  LLVM_DEBUG(dbgs() << "arg_value: ");
  arg_value->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  Value *i_iterator = builder.CreateAlloca(int_type_small, nullptr, "iterator");

  TaffoMath::pair_ftp_value<llvm::Constant *> kopp(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_wide(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_narrow(fxpret);
  TaffoMath::pair_ftp_value<llvm::Constant *> An(internal_fxpt);

  LLVM_DEBUG(dbgs() << "Initialising variables. 1/An=" << TaffoMath::compute_An_inv(-TaffoMath::cordic_exp_negative_iterations, TaffoMath::cordic_exp_positive_iterations)
                    << "\n");

  bool kopp_created = TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::Kopp, internal_fxpt, kopp.value, kopp.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, internal_fxpt, zero_wide.value, zero_wide.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, fxpret, zero_narrow.value, zero_narrow.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::compute_An_inv(-TaffoMath::cordic_exp_negative_iterations, TaffoMath::cordic_exp_positive_iterations), internal_fxpt, An.value, An.fpt);

  std::string S_ret_point = "." + std::to_string(internal_fxpt.scalarFracBitsAmt());

  if (kopp_created)
    kopp.value = TaffoMath::createGlobalConst(
        M, "kopp" + S_ret_point, kopp.fpt.scalarToLLVMType(cont), kopp.value,
        dataLayout.getPrefTypeAlignment(kopp.fpt.scalarToLLVMType(cont)));

  zero_wide.value = TaffoMath::createGlobalConst(
      M, "zero_wide" + S_ret_point, zero_wide.fpt.scalarToLLVMType(cont), zero_wide.value,
      dataLayout.getPrefTypeAlignment(zero_wide.fpt.scalarToLLVMType(cont)));

  zero_narrow.value = TaffoMath::createGlobalConst(
      M, "zero_narrow" + S_ret_point, zero_narrow.fpt.scalarToLLVMType(cont), zero_narrow.value,
      dataLayout.getPrefTypeAlignment(zero_narrow.fpt.scalarToLLVMType(cont)));

  An.value = TaffoMath::createGlobalConst(
      M, "An" + S_ret_point, An.fpt.scalarToLLVMType(cont), An.value,
      dataLayout.getPrefTypeAlignment(An.fpt.scalarToLLVMType(cont)));

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
      arctanh_2power.fpt.push_back(flttofix::FixedPointType(internal_fxpt));
      Constant *tmp = nullptr;
      auto &current_fpt = arctanh_2power.fpt.front();
      TaffoMath::createFixedPointFromConst(
          cont, ref, TaffoMath::arctanh_2power[i], internal_fxpt, tmp, current_fpt);
      arctanh_2power.value.push_back(tmp);
      LLVM_DEBUG(dbgs() << "\n");
    }

    auto arctanhArrayType = llvm::ArrayType::get(arctanh_2power.value[0]->getType(),
                                                 TaffoMath::TABLELENGHT);

    LLVM_DEBUG(dbgs() << "ArrayType  " << arctanhArrayType << "\n");
    auto arctanConstArray = llvm::ConstantArray::get(
        arctanhArrayType, llvm::ArrayRef<llvm::Constant *>(arctanh_2power.value));
    LLVM_DEBUG(dbgs() << "ConstantDataArray tmp2 " << arctanConstArray << "\n");
    auto alignement_arctanh =
        dataLayout.getPrefTypeAlignment(arctanh_2power.value[0]->getType());
    auto arctan_g =
        TaffoMath::createGlobalConst(M, "arctanh_g." + std::to_string(internal_fxpt.scalarFracBitsAmt()), arctanhArrayType,
                                     arctanConstArray, alignement_arctanh);

    pointer_to_arctanh_array = builder.CreateAlloca(arctanhArrayType, nullptr, "arctanh_array");
    pointer_to_arctanh_array->setAlignment(llvm::Align(alignement_arctanh));

    builder.CreateMemCpy(
        pointer_to_arctanh_array, llvm::Align(alignement_arctanh), arctan_g, llvm::Align(alignement_arctanh),
        TaffoMath::TABLELENGHT * (int_type->getScalarSizeInBits() >> 3));
    LLVM_DEBUG(dbgs() << "\nAdd to newf arctanh table"
                      << "\n");
  }

  BasicBlock *init = BasicBlock::Create(cont, "init", newfs);
  builder.CreateBr(init);
  builder.SetInsertPoint(init);
  LLVM_DEBUG(dbgs() << "Create init"
                    << "\n");
  arg.value = arg_value;
  BasicBlock *finalize = BasicBlock::Create(cont, "finalize", newfs);
  // handle unsigned arg
  if (!fxparg.scalarIsSigned()) {
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), ConstantInt::get(int_type, 1)), arg_value);
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
    // builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), internal_fxpt.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), arg_value);

    auto zero_arg_wide = builder.CreateLoad(getElementTypeFromValuePointer(zero_wide.value), zero_wide.value, "zero_wide");
    LLVM_DEBUG(dbgs() << "zero_arg_wide: ");
    zero_arg_wide->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto zero_arg_narrow = builder.CreateLoad(getElementTypeFromValuePointer(zero_narrow.value), zero_narrow.value, "zero_narrow");
    LLVM_DEBUG(dbgs() << "zero_arg_narrow: ");
    zero_arg_narrow->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    LLVM_DEBUG(dbgs() << "Zero value set"
                      << "\n");

    // TODO: Add constant
    auto An_load = builder.CreateLoad(getElementTypeFromValuePointer(An.value), An.value, "An");
    // Initialise x and y to the initial constant (which depends on the amount of iterations we do)
    // x=An
    builder.CreateStore(An_load, x_value.value);
    // y=An
    builder.CreateStore(An_load, y_value.value);

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

    builder.CreateStore(zero_arg_narrow, i_iterator);

    LLVM_DEBUG(dbgs() << "Iterator set"
                      << "\n");

    builder.CreateBr(check_loop_negatives);
    builder.SetInsertPoint(check_loop_negatives);

    auto iterator_value = builder.CreateLoad(getElementTypeFromValuePointer(i_iterator), i_iterator, "iterator_value_loop1");

    // Check whether i < m; if so, go to loop body. Else, go to positive loop.
    Value *iIsLessThanM = builder.CreateICmpSLT(
        iterator_value,
        ConstantInt::get(int_type_small, TaffoMath::cordic_exp_negative_iterations), "loop_condition_negatives");

    // Execute the loop if i < m; else, go to the positive loop.
    builder.CreateCondBr(iIsLessThanM, loop_body_negatives,
                         check_loop_positives);
    {
      builder.SetInsertPoint(loop_body_negatives);

      LLVM_DEBUG(dbgs() << "Start negative loop body"
                        << "\n");

      // Current argument value
      auto arg_value_load = builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value, "arg_prev_loop1");
      // Current x and y values
      auto x_value_load = builder.CreateLoad(getElementTypeFromValuePointer(x_value.value), x_value.value, "x_prev_loop1");
      auto y_value_load = builder.CreateLoad(getElementTypeFromValuePointer(y_value.value), y_value.value, "y_prev_loop1");


      // sign = arg >= 0 ? 1 : -1;
      Value *update_sign = builder.CreateSelect(
          builder.CreateICmpSGE(arg_value_load, zero_arg_wide, "arg_greater_zero_loop1"),
          ConstantInt::get(int_type, 1), ConstantInt::get(int_type, -1), "update_sign_loop1");

      // Value *update_sign = builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value, "update_sign");

      LLVM_DEBUG(dbgs() << "Sign set"
                        << "\n");

      // update_sign > 0 ?
      auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_arg_wide, "update_sign_greater_zero_loop1");

      LLVM_DEBUG(dbgs() << "Sign greater than zero set"
                        << "\n");

      // shift_amt = i+2 (casted to larger type since otherwise LLVM will complain)
      Value *shift_amt = builder.CreateAdd(builder.CreateZExt(
                                               iterator_value, int_type, "i_iterator_wide_loop1"),
                                           ConstantInt::get(int_type, 2), "shift_amt_loop1");

      LLVM_DEBUG(dbgs() << "Shift amount set"
                        << "\n");

      {
        // Update y. The update reads x.

        // Calculate x * (2 ^ -shift_amt)
        y_update = builder.CreateAShr(
            x_value_load, shift_amt, "y_upd_1_loop1");

        LLVM_DEBUG(dbgs() << "y_update 1 calculated"
                          << "\n");

        // Calculate x - x * (2 ^ -shift_amt)
        y_update = builder.CreateSub(
            x_value_load, y_update, "y_upd_2_loop1");

        LLVM_DEBUG(dbgs() << "y_update 2 calculated"
                          << "\n");

        // Calculate (update_sign > 0 ? -(x - x * (2 ^ -shift_amt)) : (x - x * (2 ^ -shift_amt)));
        y_update = builder.CreateSelect(
            update_sign_greater_zero, builder.CreateSub(zero_arg_wide, y_update, "minus_y_upd_2_loop1"), y_update, "y_upd_3_loop1");

        LLVM_DEBUG(dbgs() << "y_update 3 calculated"
                          << "\n");

        // y_{k+1} = y_k + y_update. Set to temp value since we will need to use y next.
        y_update = builder.CreateAdd(
            y_value_load, y_update, "y_upd_4_loop1");

        LLVM_DEBUG(dbgs() << "y_update 4 calculated"
                          << "\n");
      }

      {
        // Update x. The update reads y.

        // Calculate y * (2 ^ -shift_amt)
        x_update = builder.CreateAShr(
            y_value_load, shift_amt, "x_upd_1_loop1");

        LLVM_DEBUG(dbgs() << "x_update 1 calculated"
                          << "\n");

        // Calculate y - y * (2 ^ -shift_amt)
        x_update = builder.CreateSub(
            y_value_load, x_update, "x_upd_2_loop1");

        LLVM_DEBUG(dbgs() << "x_update 2 calculated"
                          << "\n");

        // Calculate (update_sign > 0 ? -(y - y * (2 ^ -shift_amt)) : (y - y * (2 ^ -shift_amt)));
        x_update = builder.CreateSelect(
            update_sign_greater_zero, builder.CreateSub(zero_arg_wide, x_update, "minus_x_upd_2_loop1"), x_update, "x_upd_3_loop1");

        LLVM_DEBUG(dbgs() << "x_update 3 calculated"
                          << "\n");

        // x_{k+1} = x_k + x_update
        x_update =
            builder.CreateAdd(x_value_load, x_update, "x_upd_4_loop1");

        LLVM_DEBUG(dbgs() << "x_update 4 calculated"
                          << "\n");
      }

      // Store y_update into y
      builder.CreateStore(y_update, y_value.value);

      LLVM_DEBUG(dbgs() << "y_update stored"
                        << "\n");

      // Store x_update into x
      builder.CreateStore(x_update, x_value.value);

      LLVM_DEBUG(dbgs() << "x_update stored"
                        << "\n");

      /*
        The two parts where we update z and increment the counter are identical for the negative and positive loops and could theoretically be made into a single subroutine.
        However, we want to avoid checking where we are each time, so we duplicate the code.
      */

      {
        // Update z (= arg)

        // Calculate arctanh_2power[i]
        Value *z_update = builder.CreateGEP(getElementTypeFromValuePointer(pointer_to_arctanh_array), pointer_to_arctanh_array,
                                            {zero_arg_wide, iterator_value}, "arctanh_2power_i_pointer_loop1");

        LLVM_DEBUG(dbgs() << "z_update: ");
        z_update->print(dbgs(), true);
        LLVM_DEBUG(dbgs() << "\n");

        LLVM_DEBUG(dbgs() << "z_update 1 calculated"
                          << "\n");

        z_update = builder.CreateLoad(getElementTypeFromValuePointer(z_update), z_update, "arctanh_2power_i_loop1");

        LLVM_DEBUG(dbgs() << "z_update 2 calculated"
                          << "\n");

        z_update = builder.CreateSelect(
            update_sign_greater_zero, builder.CreateSub(zero_arg_wide, z_update, "minus_arctanh_2power_i_loop1"), z_update, "arg_update_loop1");

        LLVM_DEBUG(dbgs() << "z_update 3 calculated"
                          << "\n");

        builder.CreateStore(
            builder.CreateAdd(z_update, arg_value_load, "arg_increment_loop1"), arg_value);

        LLVM_DEBUG(dbgs() << "z_update stored"
                          << "\n");
      }

      // i++
      builder.CreateStore(builder.CreateAdd(iterator_value,
                                            ConstantInt::get(int_type_small, 1), "iterator_value_next_loop1"),
                          i_iterator);

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

    iterator_value = builder.CreateLoad(getElementTypeFromValuePointer(i_iterator), i_iterator, "iterator_value_loop2");

    // Check whether i < (m+n); if so, go to loop body. Else, go to positive loop.
    Value *iIsLessThanN = builder.CreateICmpSLT(
        iterator_value,
        ConstantInt::get(int_type_small, TaffoMath::cordic_exp_total_iterations), "loop_condition_positives");

    // Execute the loop if i < m+n; else, go to the end of the function.
    builder.CreateCondBr(iIsLessThanN, loop_body_positives,
                         finalize);
    {
      builder.SetInsertPoint(loop_body_positives);

      LLVM_DEBUG(dbgs() << "Start positive loop body"
                        << "\n");

      // Current argument value
      auto arg_value_load = builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value, "arg_prev_loop2");
      // Current x and y values
      auto x_value_load = builder.CreateLoad(getElementTypeFromValuePointer(x_value.value), x_value.value, "x_prev_loop2");
      auto y_value_load = builder.CreateLoad(getElementTypeFromValuePointer(y_value.value), y_value.value, "y_prev_loop2");


      // sign = arg >= 0 ? 1 : -1;
      Value *update_sign = builder.CreateSelect(
          builder.CreateICmpSGE(arg_value_load, zero_arg_wide, "arg_greater_zero_loop2"),
          ConstantInt::get(int_type, 1), ConstantInt::get(int_type, -1), "update_sign_loop2");

      LLVM_DEBUG(dbgs() << "Sign set"
                        << "\n");

      // update_sign > 0 ?
      auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_arg_wide, "update_sign_greater_zero_loop2");

      LLVM_DEBUG(dbgs() << "Sign greater than zero set"
                        << "\n");

      // shift_amt = i-m since we do not reset i (again, casted to larger type since otherwise LLVM will complain)
      Value *shift_amt = builder.CreateSub(builder.CreateZExt(
                                               iterator_value, int_type, "i_iterator_wide_loop2"),
                                           ConstantInt::get(int_type, TaffoMath::cordic_exp_negative_iterations), "shift_amt_loop2");

      LLVM_DEBUG(dbgs() << "Shift amount set"
                        << "\n");

      {
        // Update y. The update reads x.

        // Calculate x * (2 ^ -shift_amt)
        y_update = builder.CreateAShr(
            x_value_load, shift_amt, "y_upd_1_loop2");

        LLVM_DEBUG(dbgs() << "y_update 1 calculated"
                          << "\n");

        // Calculate (update_sign > 0 ? -(x - x * (2 ^ -shift_amt)) : (x - x * (2 ^ -shift_amt)));
        y_update = builder.CreateSelect(
            update_sign_greater_zero, builder.CreateSub(zero_arg_wide, y_update, "minus_y_upd_1_loop2"), y_update, "y_upd_2_loop2");

        LLVM_DEBUG(dbgs() << "y_update 2 calculated"
                          << "\n");

        // y_{k+1} = y_k + y_update. Set to temp value since we will need to use y next.
        y_update = builder.CreateAdd(
            y_value_load, y_update, "y_upd_3_loop2");

        LLVM_DEBUG(dbgs() << "y_update 3 calculated"
                          << "\n");
      }

      {
        // Update x. The update reads y.

        // Calculate y * (2 ^ -shift_amt)
        x_update = builder.CreateAShr(
            y_value_load, shift_amt, "x_upd_1_loop2");

        LLVM_DEBUG(dbgs() << "x_update 1 calculated"
                          << "\n");

        // Calculate (update_sign > 0 ? -(y - y * (2 ^ -shift_amt)) : (y - y * (2 ^ -shift_amt)));
        x_update = builder.CreateSelect(
            update_sign_greater_zero, builder.CreateSub(zero_arg_wide, x_update, "minus_x_upd_1_loop2"), x_update, "x_upd_2_loop2");

        LLVM_DEBUG(dbgs() << "x_update 2 calculated"
                          << "\n");

        // x_{k+1} = x_k + x_update
        x_update =
            builder.CreateAdd(x_value_load, x_update, "x_upd_3_loop2");

        LLVM_DEBUG(dbgs() << "x_update 3 calculated"
                          << "\n");
      }

      // Store y_update into y
      builder.CreateStore(y_update, y_value.value);

      // Store x_update into x
      builder.CreateStore(x_update, x_value.value);

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
                                            {zero_arg_wide, iterator_value}, "arctanh_2power_i_pointer_loop2");

        LLVM_DEBUG(dbgs() << "z_update: ");
        z_update->print(dbgs(), true);
        LLVM_DEBUG(dbgs() << "\n");

        LLVM_DEBUG(dbgs() << "z_update 1 calculated"
                          << "\n");

        z_update = builder.CreateLoad(getElementTypeFromValuePointer(z_update), z_update, "arctanh_2power_i_loop2");

        LLVM_DEBUG(dbgs() << "z_update 2 calculated"
                          << "\n");

        z_update = builder.CreateSelect(
            update_sign_greater_zero, builder.CreateSub(zero_arg_wide, z_update, "minus_arctanh_2power_i_loop2"), z_update, "arg_update_loop2");

        LLVM_DEBUG(dbgs() << "z_update 3 calculated"
                          << "\n");

        builder.CreateStore(
            builder.CreateAdd(z_update, arg_value_load, "arg_increment_loop1"), arg_value);

        LLVM_DEBUG(dbgs() << "z_update stored"
                          << "\n");
      }

      // i++
      builder.CreateStore(builder.CreateSub(iterator_value,
                                            ConstantInt::get(int_type_small, 1), "iterator_value_next_loop1"),
                          i_iterator);
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
    builder.CreateStore(builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), internal_fxpt.scalarFracBitsAmt() - truefxpret.scalarFracBitsAmt()), arg_value);
  } else if (internal_fxpt.scalarFracBitsAmt() < truefxpret.scalarFracBitsAmt()) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), truefxpret.scalarFracBitsAmt() - internal_fxpt.scalarFracBitsAmt()), arg_value);
  }*/

  LLVM_DEBUG(dbgs() << "arg_value before shift: ");
  arg_value->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  auto ret = builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value, "arg_value_final");

  LLVM_DEBUG(dbgs() << "ret: ");
  ret->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // Shift right the result to realign the fractional part
  // builder.CreateLShr(arg_value, internal_fxpt.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt(), "output");
  arg_value = builder.CreateLShr(ret, ConstantInt::get(int_type, internal_fxpt.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), "arg_value_final_shifted");

  LLVM_DEBUG(dbgs() << "arg_value after shift: ");
  ret->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // Allocate return value
  // Value *return_value = builder.CreateAlloca(int_type_small, nullptr, "return_value");

  arg_value = builder.CreateTrunc(ret, int_type_small, "output");
  LLVM_DEBUG(dbgs() << "arg_value: ");
  arg_value->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // Value *arg_value = builder.CreateAlloca(int_type, nullptr, "arg");

  BasicBlock *end = BasicBlock::Create(cont, "end", newfs);
  builder.CreateBr(end);
  builder.SetInsertPoint(end);
  builder.CreateRet(arg_value);
  return true;
}
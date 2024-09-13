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
  // auto internal_fxpt = flttofix::FixedPointType(true, fxpret.scalarBitsAmt() - 2, fxpret.scalarBitsAmt());
  /*
    In case the argument is positive we can use the same data type for x and y, as they will end up at a similar magnitude.

    In case the argument is negative, x and y will still end up at a similar magnitude, but with opposite signs.
    This means that we subtract one from the other and the return value will be close to 0 and we cannot rely on the estimated range for the output.

    The solution for now is to just use an intermediate fixed point type with a larger number of bits: we use 64 bits in total. We estimated that x and y may get up to about 20'000 for an exponent of -15; this means that they will fit into a data type with 16 bits in the integer part (i.e. 15 bits for the integer part and 1 bit for the sign).
  */
  auto internal_fxpt = flttofix::FixedPointType(true, 64 - 16, 64);

  // create local variable
  // TODO: Check bit width for this
  TaffoMath::pair_ftp_value<llvm::Value *> x_value(fxpret);
  TaffoMath::pair_ftp_value<llvm::Value *> y_value(fxpret);
  x_value.value = builder.CreateAlloca(int_type, nullptr, "x");
  y_value.value = builder.CreateAlloca(int_type, nullptr, "y");

  Value *arg_value = builder.CreateAlloca(int_type, nullptr, "arg");
  builder.CreateStore(newfs->getArg(0), arg_value);
  Value *i_iterator = builder.CreateAlloca(int_type, nullptr, "iterator");

  // create pi variable
  TaffoMath::pair_ftp_value<llvm::Constant *> kopp(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Constant *> zero(fxpret);
  TaffoMath::pair_ftp_value<llvm::Constant *> An(fxpret);

  bool kopp_created = TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::Kopp, internal_fxpt, kopp.value, kopp.fpt);
  bool zero_created = TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, fxpret, zero.value, zero.fpt);
  bool An_created = TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::compute_An(-TaffoMath::cordic_exp_negative_iterations, TaffoMath::cordic_exp_positive_iterations), fxpret, An.value, zero.fpt);

  std::string S_ret_point = "." + std::to_string(fxpret.scalarFracBitsAmt());

  if (kopp_created)
    kopp.value = TaffoMath::createGlobalConst(
        M, "kopp" + S_ret_point, kopp.fpt.scalarToLLVMType(cont), kopp.value,
        dataLayout.getPrefTypeAlignment(kopp.fpt.scalarToLLVMType(cont)));

  zero.value = TaffoMath::createGlobalConst(
      M, "zero" + S_ret_point, zero.fpt.scalarToLLVMType(cont), zero.value,
      dataLayout.getPrefTypeAlignment(zero.fpt.scalarToLLVMType(cont)));

  zero.value = TaffoMath::createGlobalConst(
      M, "An" + S_ret_point, An.fpt.scalarToLLVMType(cont), An.value,
      dataLayout.getPrefTypeAlignment(An.fpt.scalarToLLVMType(cont)));

  /** create arctanh table
   **/
  LLVM_DEBUG(dbgs() << "Create arctanh table"
                    << "\n");
  TaffoMath::pair_ftp_value<llvm::Constant *,
                            TaffoMath::TABLELENGHT>
      arctanh_2power;
  llvm::AllocaInst *pointer_to_array = nullptr;

  if (!MathZFlag) {
    for (int i = 0; i < TaffoMath::TABLELENGHT; i++) {
      arctanh_2power.fpt.push_back(flttofix::FixedPointType(fxpret));
      Constant *tmp = nullptr;
      auto &current_fpt = arctanh_2power.fpt.front();
      TaffoMath::createFixedPointFromConst(
          cont, ref, TaffoMath::arctanh_2power[i], internal_fxpt, tmp, current_fpt);
      arctanh_2power.value.push_back(tmp);
      LLVM_DEBUG(dbgs() << i << ")");
    }


    auto arctanArrayType = llvm::ArrayType::get(arctanh_2power.value[0]->getType(),
                                                TaffoMath::TABLELENGHT);

    LLVM_DEBUG(dbgs() << "ArrayType  " << arctanArrayType << "\n");
    auto arctanConstArray = llvm::ConstantArray::get(
        arctanArrayType, llvm::ArrayRef<llvm::Constant *>(arctanh_2power.value));
    LLVM_DEBUG(dbgs() << "ConstantDataArray tmp2 " << arctanConstArray << "\n");
    auto alignement_arctanh =
        dataLayout.getPrefTypeAlignment(arctanh_2power.value[0]->getType());
    auto arctan_g =
        TaffoMath::createGlobalConst(M, "arctanh_g." + std::to_string(internal_fxpt.scalarFracBitsAmt()), arctanArrayType,
                                     arctanConstArray, alignement_arctan);

    pointer_to_array = builder.CreateAlloca(arctanArrayType);
    pointer_to_array->setAlignment(llvm::Align(alignement_arctanh));

    builder.CreateMemCpy(
        pointer_to_array, llvm::Align(alignement_arctanh), arctan_g, llvm::Align(alignement_arctanh),
        TaffoMath::TABLELENGHT * (int_type->getScalarSizeInBits() >> 3));
    LLVM_DEBUG(dbgs() << "\nAdd to newf arctan table"
                      << "\n");
  }

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

  // TODO: Handle sinh, cosh, etc.

  // TODO: Handle special cases

  // calculate sin and cos
  if (!MathZFlag) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(arg_value), arg_value), internal_fxpt.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), arg_value);

    auto zero_arg = builder.CreateLoad(getElementTypeFromValuePointer(zero.value), zero.value);
    // TODO: Add constant
    // Initialise x and y to the initial constant (which depends on the amount of iterations we do)
    // x=An
    builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(An.value), An.value), x_value.value);
    // y=An
    builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(An.value), An.value), y_value.value);

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

    // TODO: repeat iterations 4, 13, 40

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
      Value *shift_amt = builder.CreateSub(
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
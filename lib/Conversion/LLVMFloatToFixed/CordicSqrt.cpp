/*
    Hyperbolic CORDIC for sqrt
*/

#include "CordicSqrt.h"
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

bool createSqrt(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
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

    auto internal_fxpt = flttofix::FixedPointType(true, flttofix::cordic_sqrt_internal_width_fractional, flttofix::cordic_sqrt_internal_width);

    auto int_type_wide = internal_fxpt.scalarToLLVMType(cont);
    LLVM_DEBUG(dbgs() << "Internal fixed point type: ");
    int_type_wide->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto int_type_narrow = fxpret.scalarToLLVMType(cont);
    LLVM_DEBUG(dbgs() << "Return fixed point type: ");
    int_type_narrow->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    // Generate strings for constants names
    std::string S_arg_point = "." + std::to_string(fxparg.scalarFracBitsAmt());
    std::string S_ret_point = "." + std::to_string(fxpret.scalarFracBitsAmt());
    std::string S_int_point = "." + std::to_string(internal_fxpt.scalarFracBitsAmt());

    // ----------------------------------------------------

    // The pointer to the value that is actually returned.
    Value *return_value_ptr = builder.CreateAlloca(int_type_narrow, nullptr, "return_value_ptr");

    // Pointer to the argument
    Value *arg_ptr = builder.CreateAlloca(int_type_narrow, nullptr, "arg");
    builder.CreateStore(newfs->getArg(0), arg_ptr);

    LLVM_DEBUG(dbgs() << "arg_ptr: ");
    arg_ptr->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    LLVM_DEBUG(dbgs() << "Argument is unsigned: shifting it to the right by 1 bit\n");
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), ConstantInt::get(int_type_narrow, 1), "arg_shifted_was_unsigned"), arg_ptr);
    fxparg.scalarFracBitsAmt() = fxparg.scalarFracBitsAmt() - 1;
    fxparg.scalarIsSigned() = true;

    // ----------------------------------------------------
    // Some variables we will need to handle special cases.
    // More variables will be declared later.

    // Pointer to one (for comparison with the argument)
    TaffoMath::pair_ftp_value<llvm::Constant *> one_ptr_arg(fxparg);
    bool one_ptr_arg_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 1.0, fxparg, one_ptr_arg.value, one_ptr_arg.fpt);
    if (one_ptr_arg_created)
        one_ptr_arg.value = TaffoMath::createGlobalConst(
            M, "one_ptr_arg" + S_arg_point, one_ptr_arg.fpt.scalarToLLVMType(cont), one_ptr_arg.value,
            dataLayout.getPrefTypeAlignment(one_ptr_arg.fpt.scalarToLLVMType(cont)));
    // Pointer to one (for returning)
    TaffoMath::pair_ftp_value<llvm::Constant *> one_ptr_ret(fxparg);
    bool one_ptr_ret_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 1.0, fxparg, one_ptr_ret.value, one_ptr_ret.fpt);
    if (one_ptr_ret_created)
        one_ptr_ret.value = TaffoMath::createGlobalConst(
            M, "one_ptr_arg" + S_arg_point, one_ptr_ret.fpt.scalarToLLVMType(cont), one_ptr_ret.value,
            dataLayout.getPrefTypeAlignment(one_ptr_ret.fpt.scalarToLLVMType(cont)));

    // ----------------------------------------------------
    // Basic blocks

    // Block for the initialization of the preparation loop (check if the argument is negative, check if the argument is 1, check if the argument is 0, enter first loop)
    BasicBlock *init = BasicBlock::Create(cont, "init", newfs);

    // Blocks where we check loop boundaries of the preparation loop
    BasicBlock *check_small_arg = BasicBlock::Create(cont, "check_small_arg", newfs);
    BasicBlock *check_big_arg = BasicBlock::Create(cont, "check_big_arg", newfs);

    // Preparation loop body
    BasicBlock *preparation_loop_lower = BasicBlock::Create(cont, "preparation_loop_lower", newfs);
    BasicBlock *preparation_loop_upper = BasicBlock::Create(cont, "preparation_loop_upper", newfs);

    // Block for the initialization of the main loop
    BasicBlock *init_main = BasicBlock::Create(cont, "init_main", newfs);

    // Block where we check loop boundaries of the main loop
    BasicBlock *check_loop = BasicBlock::Create(cont, "check_loop", newfs);

    // Main loop body (+ check if repetition is necessary)
    BasicBlock *loop_body = BasicBlock::Create(cont, "loop_body", newfs);

    // Repetition block
    BasicBlock *repetition = BasicBlock::Create(cont, "repetition", newfs);

    // Itaration block
    BasicBlock *iteration = BasicBlock::Create(cont, "iteration", newfs);

    // End block
    BasicBlock *end = BasicBlock::Create(cont, "end", newfs);


    // Blocks for special cases

    BasicBlock *checkArgIsZero = BasicBlock::Create(cont, "check_arg_is_zero", newfs);
    BasicBlock *argIsZero = BasicBlock::Create(cont, "arg_is_zero", newfs);

    BasicBlock *checkArgIsOne = BasicBlock::Create(cont, "check_arg_is_one", newfs);
    BasicBlock *argIsOne = BasicBlock::Create(cont, "arg_is_one", newfs);

    BasicBlock *checkArgIsNegative = BasicBlock::Create(cont, "check_arg_is_negative", newfs);
    BasicBlock *argIsNegative = BasicBlock::Create(cont, "arg_is_negative", newfs);


    // TODO arg boundaries and special cases

    // ----------------------------------------------------
    // Initialisation of the preparation loop

    LLVM_DEBUG(dbgs() << "Create init"
                    << "\n");
    builder.CreateBr(init);
    builder.SetInsertPoint(init);

    // Support variables that we use internally
    // The argument is created above

    // The two updaters that oscillate
    TaffoMath::pair_ftp_value<llvm::Value *> x_ptr(internal_fxpt);
    TaffoMath::pair_ftp_value<llvm::Value *> y_ptr(internal_fxpt);
    x_ptr.value = builder.CreateAlloca(int_type_wide, nullptr, "x");
    y_ptr.value = builder.CreateAlloca(int_type_wide, nullptr, "y");

    Value *k_ptr = builder.CreateAlloca(int_type_narrow, nullptr, "k");

    // pointer to the current iteration counter
    Value *i_ptr = builder.CreateAlloca(int_type_narrow, nullptr, "i_ptr");

    // pointer to the shift amount in the preparation loop
    Value *shift_pre_ptr = builder.CreateAlloca(int_type_narrow, nullptr, "shift_pre_ptr");

    Value *output_temp;

    // Pointer to 0.5 in the internal (wide) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> lower_ptr_wide(internal_fxpt);
    // Pointer to 0.5 in the return (narrow) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> lower_ptr_narrow(fxpret);
    // Pointer to 2 in the internal (wide) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> upper_ptr_wide(internal_fxpt);
    // Pointer to 2 in the return (narrow) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> upper_ptr_narrow(fxpret);
    // Pointer to zero in the internal (wide) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> zero_ptr_wide(internal_fxpt);
    // Pointer to zero in the return (narrow) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> zero_ptr_narrow(fxpret);
    // Pointer to 0.25 in the internal (wide) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> quarter_ptr_wide(internal_fxpt);
    // Pointer to 0.25 in the return (narrow) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> quarter_ptr_narrow(fxpret);

    // ----------------------------------------------------

    // Create the constants 0.5 and 2 and 0 and 0.25
    bool lower_ptr_wide_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 0.5, internal_fxpt, lower_ptr_wide.value, lower_ptr_wide.fpt);
    bool lower_ptr_narrow_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 0.5, fxpret, lower_ptr_narrow.value, lower_ptr_narrow.fpt);
    bool upper_ptr_wide_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 2.0, internal_fxpt, upper_ptr_wide.value, upper_ptr_wide.fpt);
    bool upper_ptr_narrow_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 2.0, fxpret, upper_ptr_narrow.value, upper_ptr_narrow.fpt);
    bool zero_ptr_wide_created = TaffoMath::createFixedPointFromConst(
        cont, ref, TaffoMath::zero, internal_fxpt, zero_ptr_wide.value, zero_ptr_wide.fpt);
    bool zero_ptr_narrow_created = TaffoMath::createFixedPointFromConst(
        cont, ref, TaffoMath::zero, fxpret, zero_ptr_narrow.value, zero_ptr_narrow.fpt);
    bool quarter_ptr_wide_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 0.25, internal_fxpt, quarter_ptr_wide.value, quarter_ptr_wide.fpt);
    bool quarter_ptr_narrow_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 0.25, fxpret, quarter_ptr_narrow.value, quarter_ptr_narrow.fpt);

    if (!(lower_ptr_wide_created && lower_ptr_narrow_created && upper_ptr_wide_created && upper_ptr_narrow_created && zero_ptr_wide_created && zero_ptr_narrow_created && quarter_ptr_wide_created && quarter_ptr_narrow_created)) {
        LLVM_DEBUG(dbgs() << "===== ERROR: Could not create one or more of the initialisation constants\n");
        llvm_unreachable("Could not create one or more of the initialisation constants. Sqrt cannot continue.");
        return false;
    }

    lower_ptr_wide.value = TaffoMath::createGlobalConst(
        M, "lower_ptr_wide" + S_int_point, lower_ptr_wide.fpt.scalarToLLVMType(cont), lower_ptr_wide.value,
        dataLayout.getPrefTypeAlignment(lower_ptr_wide.fpt.scalarToLLVMType(cont)));
    lower_ptr_narrow.value = TaffoMath::createGlobalConst(
        M, "lower_ptr_narrow" + S_ret_point, lower_ptr_narrow.fpt.scalarToLLVMType(cont), lower_ptr_narrow.value,
        dataLayout.getPrefTypeAlignment(lower_ptr_narrow.fpt.scalarToLLVMType(cont)));
    upper_ptr_wide.value = TaffoMath::createGlobalConst(
        M, "upper_ptr_wide" + S_int_point, upper_ptr_wide.fpt.scalarToLLVMType(cont), upper_ptr_wide.value,
        dataLayout.getPrefTypeAlignment(upper_ptr_wide.fpt.scalarToLLVMType(cont)));
    upper_ptr_narrow.value = TaffoMath::createGlobalConst(
        M, "upper_ptr_narrow" + S_ret_point, upper_ptr_narrow.fpt.scalarToLLVMType(cont), upper_ptr_narrow.value,
        dataLayout.getPrefTypeAlignment(upper_ptr_narrow.fpt.scalarToLLVMType(cont)));
    zero_ptr_wide.value = TaffoMath::createGlobalConst(
        M, "zero_ptr_wide" + S_int_point, zero_ptr_wide.fpt.scalarToLLVMType(cont), zero_ptr_wide.value,
        dataLayout.getPrefTypeAlignment(zero_ptr_wide.fpt.scalarToLLVMType(cont)));
    zero_ptr_narrow.value = TaffoMath::createGlobalConst(
        M, "zero_ptr_narrow" + S_ret_point, zero_ptr_narrow.fpt.scalarToLLVMType(cont), zero_ptr_narrow.value,
        dataLayout.getPrefTypeAlignment(zero_ptr_narrow.fpt.scalarToLLVMType(cont)));

    // ----------------------------------------------------
    LLVM_DEBUG(dbgs() << "Starting preparation loop"
                    << "\n");

    auto lower_value_wide = builder.CreateLoad(getElementTypeFromValuePointer(lower_ptr_wide.value), lower_ptr_wide.value, "lower_wide");
    LLVM_DEBUG(dbgs() << "lower_value_wide: ");
    lower_value_wide->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto lower_value_narrow = builder.CreateLoad(getElementTypeFromValuePointer(lower_ptr_narrow.value), lower_ptr_narrow.value, "lower_narrow");
    LLVM_DEBUG(dbgs() << "lower_value_narrow: ");
    lower_value_narrow->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto upper_value_wide = builder.CreateLoad(getElementTypeFromValuePointer(upper_ptr_wide.value), upper_ptr_wide.value, "upper_wide");
    LLVM_DEBUG(dbgs() << "upper_value_wide: ");
    upper_value_wide->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto upper_value_narrow = builder.CreateLoad(getElementTypeFromValuePointer(upper_ptr_narrow.value), upper_ptr_narrow.value, "upper_narrow");
    LLVM_DEBUG(dbgs() << "upper_value_narrow: ");
    upper_value_narrow->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto zero_value_wide = builder.CreateLoad(getElementTypeFromValuePointer(zero_ptr_wide.value), zero_ptr_wide.value, "zero_wide");
    LLVM_DEBUG(dbgs() << "zero_value_wide: ");
    zero_value_wide->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto zero_value_narrow = builder.CreateLoad(getElementTypeFromValuePointer(zero_ptr_narrow.value), zero_ptr_narrow.value, "zero_narrow");
    LLVM_DEBUG(dbgs() << "zero_value_narrow: ");
    zero_value_narrow->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");


    LLVM_DEBUG(dbgs() << "Boundaries set"
                    << "\n");

    builder.CreateStore(zero_value_narrow, shift_pre_ptr);

    // ----------------------------------------------------
    // First loop: condition < 0.5

    builder.CreateBr(check_small_arg);
    builder.SetInsertPoint(check_small_arg);

    auto shift_pre_value = builder.CreateLoad(getElementTypeFromValuePointer(shift_pre_ptr), shift_pre_ptr, "shift_pre_value");

    auto arg_value_narrow = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "curr_arg_val_narrow_preloop");
    Value *arg_value_wide = builder.CreateShl(builder.CreateSExt(arg_value_narrow, int_type_wide, "sign_extended_arg_preloop"), internal_fxpt.scalarFracBitsAmt() - fxparg.scalarFracBitsAmt(), "curr_arg_val_wide_preloop");

    Value *isLessThanLower = builder.CreateICmpSLT(
        arg_value_narrow,
        lower_value_narrow, "loop_condition_preloop_lower");

    builder.CreateCondBr(isLessThanLower, preparation_loop_lower,
                        check_big_arg);
    
    builder.SetInsertPoint(preparation_loop_lower);

    // Shift the argument right by 2 bits
    output_temp = builder.CreateAShr(arg_value_wide, ConstantInt::get(int_type_wide, 2), "arg_value_shifted_preloop_lower");
    builder.CreateStore(output_temp, arg_ptr);

    // augument shift_pre by 2

    output_temp = builder.CreateAdd(shift_pre_value, ConstantInt::get(int_type_narrow, 2), "shift_pre_value_lower");
    
    // Store the new value of the argument
    builder.CreateStore(output_temp, shift_pre_ptr);

    builder.CreateBr(check_small_arg);

    // ----------------------------------------------------

    // Second loop: condition >= 2

    builder.SetInsertPoint(check_big_arg);

    auto isGreaterThanUpper = builder.CreateICmpSGE(
        arg_value_narrow,
        upper_value_narrow, "loop_condition_preloop_upper");
    
    builder.CreateCondBr(isGreaterThanUpper, preparation_loop_upper,
                        init_main);
    
    builder.SetInsertPoint(preparation_loop_upper);

    // Shift the argument left by 2 bits
    output_temp = builder.CreateShl(arg_value_wide, ConstantInt::get(int_type_wide, 2), "arg_value_shifted_preloop_upper");
    builder.CreateStore(output_temp, arg_ptr);

    // diminish shift_pre by 2

    output_temp = builder.CreateSub(shift_pre_value, ConstantInt::get(int_type_narrow, 2), "shift_pre_value_upper");

    // Store the new value of the argument
    builder.CreateStore(output_temp, shift_pre_ptr);

    builder.CreateBr(check_big_arg);


    // ----------------------------------------------------
    // Main loop initialisation

    builder.SetInsertPoint(init_main);

    // Set the iterator to 1
    builder.CreateStore(ConstantInt::get(int_type_narrow, 1), i_ptr);

    // Set the x and y values to arg + 0.25 and arg - 0.25 
    auto arg_value = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_value");
    auto arg_value_wide = builder.CreateShl(builder.CreateSExt(arg_value, int_type_wide, "sign_extended_arg"), internal_fxpt.scalarFracBitsAmt() - fxparg.scalarFracBitsAmt(), "arg_value_wide");

    // x = arg + 0.25
    auto x_value = builder.CreateAdd(arg_value_wide, builder.CreateLoad(getElementTypeFromValuePointer(quarter_ptr_wide.value), quarter_ptr_wide.value, "quarter_wide"), "x_value");
    builder.CreateStore(x_value, x_ptr.value);

    // y = arg - 0.25
    auto y_value = builder.CreateSub(arg_value_wide, builder.CreateLoad(getElementTypeFromValuePointer(quarter_ptr_wide.value), quarter_ptr_wide.value, "quarter_wide"), "y_value");
    builder.CreateStore(y_value, y_ptr.value);

    // Temp values to store updates
    Value *x_update;
    Value *y_update;
    Value *k_value;
    
    // set k to 4
    builder.CreateStore(ConstantInt::get(int_type_narrow, 4), k_ptr);

    // ----------------------------------------------------

    LLVM_DEBUG(dbgs() << "Start loop"
                    << "\n");

    builder.CreateBr(check_loop);
    builder.SetInsertPoint(check_loop);

    auto i_value = builder.CreateLoad(getElementTypeFromValuePointer(i_ptr), i_ptr, "i_value");
    auto i_value_wide = builder.CreateZExt(
        i_value, int_type_wide, "i_value_wide");

    // Check whether i < cordic_sqrt_total_iterations; if so, go to loop body. Else, go to the end of the function.
    Value *iIsLessThanN = builder.CreateICmpSLE(
        i_value,
        ConstantInt::get(int_type_narrow, flttofix::cordic_sqrt_total_iterations), "loop_condition");
    
    builder.CreateCondBr(iIsLessThanN, loop_body,
                        end);


    // Loop body
    
    builder.SetInsertPoint(loop_body);

    // Current argument value
    auto arg_value = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_value_curr");
    auto arg_value_wide = builder.CreateShl(builder.CreateSExt(arg_value, int_type_wide, "sign_extended_arg"), internal_fxpt.scalarFracBitsAmt() - fxparg.scalarFracBitsAmt(), "arg_value_wide_curr");

    // Current x and y values
    auto x_value = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_curr");
    auto y_value = builder.CreateLoad(getElementTypeFromValuePointer(y_ptr.value), y_ptr.value, "y_curr");

    // sign = y >= 0 ? -1 : 1;
    // Shift right until we get the most significant bit only
    Value *update_sign = builder.CreateSelect(
        builder.CreateICmpSGT(y_value, zero_value_wide, "arg_is_positive"),
        ConstantInt::get(int_type_wide, -1), ConstantInt::get(int_type_wide, 1), "update_sign");

    // update_sign > 0 ?
    auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_value_wide, "update_sign_greater_zero");

    // sign = y >= 0 ? -1 : 1;
    Value *update_sign_narrow = builder.CreateSelect(
        builder.CreateICmpSGT(y_value, zero_value_wide, "arg_is_positive_narrow"),
        ConstantInt::get(int_type_narrow, -1), ConstantInt::get(int_type_narrow, 1), "update_sign_narrow");
    
    // update_sign > 0 ?
    auto update_sign_greater_zero_narrow = builder.CreateICmpSGT(update_sign_narrow, zero_value_narrow, "update_sign_greater_zero_narrow");

    LLVM_DEBUG(dbgs() << "Sign greater than zero set"
                      << "\n");
    
    y_update = builder.CreateAShr(x_value, i_value_wide, "y_update");
    x_update = builder.CreateAShr(y_value, i_value_wide, "x_update");

    y_value = builder.CreateSelect(
        update_sign_greater_zero, builder.CreateAdd(y_value, y_update, "y_update"), builder.CreateSub(y_value, y_update, "y_update"), "y_update_select");

    x_value = builder.CreateSelect(
        update_sign_greater_zero, builder.CreateAdd(x_value, x_update, "x_update"), builder.CreateSub(x_value, x_update, "x_update"), "x_update_select");

    builder.CreateStore(y_value, y_ptr.value);
    builder.CreateStore(x_value, x_ptr.value);

    k_value = builder.CreateLoad(getElementTypeFromValuePointer(k_ptr), k_ptr, "k_value");

    Value *isIequalToK = builder.CreateICmpEQ(
        i_value,
        k_value, "loop_condition_k");

    builder.CreateCondBr(isIequalToK, repetition,
                        iteration);

    // ----------------------------------------------------

    // Repetition block

    builder.SetInsertPoint(repetition);

    // k = 3 * k + 1
    k_value = builder.CreateLoad(getElementTypeFromValuePointer(k_ptr), k_ptr, "k_value_repetition");
    k_value = builder.CreateAdd(builder.CreateShl(k_value, ConstantInt::get(int_type_narrow, 1), "k_shifted"), k_value, "3_times_k");
    k_value = builder.CreateAdd(k_value, ConstantInt::get(int_type_narrow, 1), "3_times_k_plus_1");
    builder.CreateStore(k_value, k_ptr);

    builder.CreateBr(loop_body);

    // ----------------------------------------------------

    // Iteration block

    builder.SetInsertPoint(iteration);

    // i = i + 1
    i_value = builder.CreateAdd(i_value, ConstantInt::get(int_type_narrow, 1), "i_plus_1");
    builder.CreateStore(i_value, i_ptr);

    builder.CreateBr(check_loop);

    // ----------------------------------------------------

    // End block

    builder.SetInsertPoint(end);

    // shift shift_pre by i
    shift_pre_value = builder.CreateLoad(getElementTypeFromValuePointer(shift_pre_ptr), shift_pre_ptr, "shift_pre_value_end");
    shift_pre_value = builder.CreateAShr(shift_pre_value, 1, "shift_pre_value_end_shifted");

    Value* ShiftPreGreaterThanZero = builder.CreateICmpSGT(shift_pre_value, zero_value_narrow, "shift_pre_greater_than_zero");

    // Shift x left by shift_pre
    x_value = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_value_end");
    x_value = builder.CreateSelect(ShiftPreGreaterThanZero, 
            builder.CreateShl(x_value, shift_pre_value, "x_shifted"), builder.CreateAShr(x_value, builder.CreateNeg(shift_pre_value), "x_shifted"), "x_shifted_select");

    // TODO: multiply x by 1/An (which is the return value of the function compute_An_inv)

    // Store x into return value
    auto ret = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_value_final");

    // Shift right the result to realign the fractional part
    // builder.CreateLShr(arg_ptr, internal_fxpt.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt(), "output");
    output_temp = builder.CreateAShr(ret, ConstantInt::get(int_type_wide, internal_fxpt.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), "arg_value_final_shifted");

    builder.CreateStore(output_temp, return_value_ptr);

    builder.CreateRet(builder.CreateLoad(getElementTypeFromValuePointer(return_value_ptr), return_value_ptr));
    return true;
}


} // namespace flttofix
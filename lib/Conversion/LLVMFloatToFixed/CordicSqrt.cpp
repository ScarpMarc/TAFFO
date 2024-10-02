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

    auto internal_fxpt = flttofix::FixedPointType(true, flttofix::cordic_sqrt_internal_width_fractional, flttofix::cordic_sqrt_internal_width);

    LLVM_DEBUG(dbgs() << "fxpret: " << fxpret.scalarBitsAmt() << " frac part: " << fxpret.scalarFracBitsAmt() << " difference: " << fxpret.scalarBitsAmt() - fxpret.scalarFracBitsAmt() << "\n");
    LLVM_DEBUG(dbgs() << "fxparg: " << fxparg.scalarBitsAmt() << " frac part: " << fxparg.scalarFracBitsAmt() << " difference: " << fxparg.scalarBitsAmt() - fxparg.scalarFracBitsAmt() << "\n");
    LLVM_DEBUG(dbgs() << "Internal fixed point type: " << internal_fxpt.scalarBitsAmt() << " frac part: " << internal_fxpt.scalarFracBitsAmt() << " difference: " << internal_fxpt.scalarBitsAmt() - internal_fxpt.scalarFracBitsAmt() << "\n");

    auto int_type_arg = fxparg.scalarToLLVMType(cont);
    LLVM_DEBUG(dbgs() << "Argument fixed point type: ");
    int_type_arg->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto int_type_ret = fxpret.scalarToLLVMType(cont);
    LLVM_DEBUG(dbgs() << "Return fixed point type: ");
    int_type_ret->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto int_type_internal = internal_fxpt.scalarToLLVMType(cont);
    LLVM_DEBUG(dbgs() << "internal fixed point type: ");
    int_type_internal->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");




    // Generate strings for constants names
    std::string S_arg_point = "." + std::to_string(fxparg.scalarFracBitsAmt());
    std::string S_ret_point = "." + std::to_string(fxpret.scalarFracBitsAmt());

    // ----------------------------------------------------

    // The pointer to the value that is actually returned.
    Value *return_value_ptr = builder.CreateAlloca(int_type_ret, nullptr, "return_value_ptr");

    // Pointer to the argument
    Value *arg_ptr = builder.CreateAlloca(int_type_arg, nullptr, "arg");
    builder.CreateStore(newfs->getArg(0), arg_ptr);

    LLVM_DEBUG(dbgs() << "arg_ptr: ");
    arg_ptr->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    if (!fxparg.scalarIsSigned()) {
        LLVM_DEBUG(dbgs() << "Argument is unsigned: shifting it to the right by 1 bit\n");
        builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), ConstantInt::get(int_type_arg, 1), "arg_shifted_was_unsigned"), arg_ptr);
        fxparg.scalarFracBitsAmt() = fxparg.scalarFracBitsAmt() - 1;
        fxparg.scalarIsSigned() = true;
    }


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

    // Result block
    BasicBlock *result = BasicBlock::Create(cont, "result", newfs);


    // Blocks for special cases
    BasicBlock *checkArgIsZeroNeg = BasicBlock::Create(cont, "check_arg_is_zero_neg", newfs);
    BasicBlock *argIsZeroNeg = BasicBlock::Create(cont, "arg_is_zero_neg", newfs);

    BasicBlock *checkArgIsOne = BasicBlock::Create(cont, "check_arg_is_one", newfs);
    BasicBlock *argIsOne = BasicBlock::Create(cont, "arg_is_one", newfs);

    builder.CreateBr(checkArgIsOne);
    builder.SetInsertPoint(checkArgIsOne);

    // Check if the argument is one
    Value *arg_is_one = builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), ConstantInt::get(int_type_arg, 1), "arg_is_one");

    builder.CreateCondBr(arg_is_one, argIsOne, checkArgIsZeroNeg);

    {
        builder.SetInsertPoint(argIsOne);

        // If the argument is one, return one
        LLVM_DEBUG(dbgs() << "===== Argument is one. Sqrt is one.\n");
        builder.CreateStore(ConstantInt::get(int_type_ret, 1), return_value_ptr);

        builder.CreateBr(result);
    }

    builder.SetInsertPoint(checkArgIsZeroNeg);

    // Check if the argument is zero or negative
    Value *arg_is_zero_neg = builder.CreateICmpSLE(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), ConstantInt::get(int_type_arg, 0), "arg_is_zero_neg");

    builder.CreateCondBr(arg_is_zero_neg, argIsZeroNeg, init);

    {
        builder.SetInsertPoint(argIsZeroNeg);

        // If the argument is zero or negative, return zero
        LLVM_DEBUG(dbgs() << "===== ERROR: Argument is zero or negative. Sqrt cannot continue.\n");
        builder.CreateStore(ConstantInt::get(int_type_ret, 0), return_value_ptr);

        builder.CreateBr(result);
    }


    // ----------------------------------------------------
    // Initialisation of the preparation loop

    builder.SetInsertPoint(init);

    LLVM_DEBUG(dbgs() << "Create init"
                    << "\n");

    // Support variables that we use internally
    // The argument is created above

    // The two updaters that oscillate
    TaffoMath::pair_ftp_value<llvm::Value *> x_ptr(fxpret);
    TaffoMath::pair_ftp_value<llvm::Value *> y_ptr(fxpret);
    x_ptr.value = builder.CreateAlloca(int_type_ret, nullptr, "x");
    y_ptr.value = builder.CreateAlloca(int_type_ret, nullptr, "y");

    TaffoMath::pair_ftp_value<llvm::Value *> k_ptr(internal_fxpt);
    k_ptr.value = builder.CreateAlloca(int_type_internal, nullptr, "k");

    // pointer to the current iteration counter
    TaffoMath::pair_ftp_value<llvm::Value *> i_ptr(internal_fxpt);
    i_ptr.value = builder.CreateAlloca(int_type_internal, nullptr, "i_ptr");

    // pointer to the shift amount in the preparation loop
    TaffoMath::pair_ftp_value<llvm::Value *> shift_pre_ptr(internal_fxpt);
    shift_pre_ptr.value = builder.CreateAlloca(int_type_internal, nullptr, "shift_pre_ptr");

    // Pointer to 0.5 in the return (narrow) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> lower_ptr(fxparg);
    // Pointer to 2 in the return (narrow) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> upper_ptr(fxparg);
    // Pointer to zero in the return (narrow) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> zero_ptr(fxpret);
    // Pointer to 0.25 in the return (narrow) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> quarter_ptr(fxpret);
    // Pointer to 4 in the return (narrow) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> four_ptr(fxpret);
    // Pointer to 1 in the return (narrow) fixed point type
    TaffoMath::pair_ftp_value<llvm::Constant *> one_ptr(fxparg);
    // Pointer to An
    TaffoMath::pair_ftp_value<llvm::Constant *> An_ptr(fxpret);


    // ----------------------------------------------------

    // Create the constants
    bool lower_ptr_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 0.5, fxparg, lower_ptr.value, lower_ptr.fpt);
    bool upper_ptr_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 2.0, fxparg, upper_ptr.value, upper_ptr.fpt);
    bool zero_ptr_created = TaffoMath::createFixedPointFromConst(
        cont, ref, TaffoMath::zero, fxpret, zero_ptr.value, zero_ptr.fpt);
    bool quarter_ptr_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 0.25, fxpret, quarter_ptr.value, quarter_ptr.fpt);
    bool four_ptr_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 4.0, fxparg, four_ptr.value, four_ptr.fpt);
    bool one_ptr_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 1.0, fxparg, one_ptr.value, one_ptr.fpt);
    bool An_ptr_created = TaffoMath::createFixedPointFromConst(
        cont, ref, flttofix::compute_An(fxpret.scalarFracBitsAmt()), fxpret, An_ptr.value, An_ptr.fpt);
  

    if (!(lower_ptr_created && upper_ptr_created
        && zero_ptr_created && quarter_ptr_created
        && four_ptr_created && one_ptr_created 
        && An_ptr_created)) {
        LLVM_DEBUG(dbgs() << "===== ERROR: Could not create one or more of the initialisation constants\n");
        llvm_unreachable("Could not create one or more of the initialisation constants. Sqrt cannot continue.");
        return false;
    }

    lower_ptr.value = TaffoMath::createGlobalConst(
        M, "lower_ptr" + S_arg_point, lower_ptr.fpt.scalarToLLVMType(cont), lower_ptr.value,
        dataLayout.getPrefTypeAlignment(lower_ptr.fpt.scalarToLLVMType(cont)));
    upper_ptr.value = TaffoMath::createGlobalConst(
        M, "upper_ptr" + S_arg_point, upper_ptr.fpt.scalarToLLVMType(cont), upper_ptr.value,
        dataLayout.getPrefTypeAlignment(upper_ptr.fpt.scalarToLLVMType(cont)));
    zero_ptr.value = TaffoMath::createGlobalConst(
        M, "zero_ptr" + S_ret_point, zero_ptr.fpt.scalarToLLVMType(cont), zero_ptr.value,
        dataLayout.getPrefTypeAlignment(zero_ptr.fpt.scalarToLLVMType(cont)));
    quarter_ptr.value = TaffoMath::createGlobalConst(
        M, "quarter_ptr" + S_ret_point, quarter_ptr.fpt.scalarToLLVMType(cont), quarter_ptr.value,
        dataLayout.getPrefTypeAlignment(quarter_ptr.fpt.scalarToLLVMType(cont)));
    four_ptr.value = TaffoMath::createGlobalConst(
        M, "four_ptr" + S_ret_point, four_ptr.fpt.scalarToLLVMType(cont), four_ptr.value,
        dataLayout.getPrefTypeAlignment(four_ptr.fpt.scalarToLLVMType(cont)));
    one_ptr.value = TaffoMath::createGlobalConst(
        M, "one_ptr" + S_arg_point, one_ptr.fpt.scalarToLLVMType(cont), one_ptr.value,
        dataLayout.getPrefTypeAlignment(one_ptr.fpt.scalarToLLVMType(cont)));

    // ----------------------------------------------------
    LLVM_DEBUG(dbgs() << "Starting preparation loop"
                    << "\n");

    auto lower_value = builder.CreateLoad(getElementTypeFromValuePointer(lower_ptr.value), lower_ptr.value, "lower");
    LLVM_DEBUG(dbgs() << "lower_value: ");
    lower_value->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto upper_value = builder.CreateLoad(getElementTypeFromValuePointer(upper_ptr.value), upper_ptr.value, "upper");
    LLVM_DEBUG(dbgs() << "upper_value: ");
    upper_value->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto zero_value = builder.CreateLoad(getElementTypeFromValuePointer(zero_ptr.value), zero_ptr.value, "zero");
    LLVM_DEBUG(dbgs() << "zero_value: ");
    zero_value->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    LLVM_DEBUG(dbgs() << "Boundaries set"
                    << "\n");

    builder.CreateStore(ConstantInt::get(int_type_internal, 0), shift_pre_ptr.value);

    Value *arg_value = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "curr_arg_val");
    Value *shift_pre_value = builder.CreateAlloca(int_type_internal, nullptr, "shift_pre_value");
    shift_pre_value = builder.CreateLoad(getElementTypeFromValuePointer(shift_pre_ptr.value), shift_pre_ptr.value, "shift_pre_value");
    // ----------------------------------------------------
    // First loop: condition < 0.5

    builder.CreateBr(check_small_arg);
    {
        builder.SetInsertPoint(check_small_arg);

        shift_pre_value = builder.CreateLoad(getElementTypeFromValuePointer(shift_pre_ptr.value), shift_pre_ptr.value, "shift_pre_value");

        arg_value = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "curr_arg_val_narrow_preloop");

        Value *isLessThanLower = builder.CreateICmpSLT(
            arg_value,
            lower_value, "loop_condition_preloop_lower");

        builder.CreateCondBr(isLessThanLower, preparation_loop_lower,
                            check_big_arg);
    }
    
    {
        builder.SetInsertPoint(preparation_loop_lower);

        // Shift the argument left by 2 bits
        arg_value = builder.CreateShl(arg_value, ConstantInt::get(int_type_arg, 2), "arg_value_shifted_preloop_lower");

        // augument shift_pre by 2

        //shift_pre_value = builder.CreateAdd(shift_pre_value, ConstantInt::get(int_type_ret, 2), "shift_pre_value_lower");
        
        // Store the new value of the argument
        builder.CreateStore(builder.CreateAdd(shift_pre_value, ConstantInt::get(int_type_internal, 2), "shift_pre_value_lower"), shift_pre_ptr.value);
        builder.CreateStore(arg_value, arg_ptr);

        builder.CreateBr(check_small_arg);

    }

    // ----------------------------------------------------

    // Second loop: condition >= 2
    {

        builder.SetInsertPoint(check_big_arg);

        shift_pre_value = builder.CreateLoad(getElementTypeFromValuePointer(shift_pre_ptr.value), shift_pre_ptr.value, "shift_pre_value");

        arg_value = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "curr_arg_val_narrow_preloop");

        auto isGreaterThanUpper = builder.CreateICmpSGE(
            arg_value,
            upper_value, "loop_condition_preloop_upper");
        
        builder.CreateCondBr(isGreaterThanUpper, preparation_loop_upper,
                            init_main);

    }

    {
    
        builder.SetInsertPoint(preparation_loop_upper);

        // Shift the argument right by 2 bits
        arg_value = builder.CreateAShr(arg_value, ConstantInt::get(int_type_arg, 2), "arg_value_shifted_preloop_upper");

        // diminish shift_pre by 2

        //shift_pre_value = builder.CreateSub(shift_pre_value, ConstantInt::get(int_type_ret, 2), "shift_pre_value_upper");

        auto shift_type = shift_pre_value->getType();
        LLVM_DEBUG(dbgs() << "Shift type: ");
        shift_type->print(dbgs(), true);
        LLVM_DEBUG(dbgs() << "\n");
            
        // Store the new value of the argument
        builder.CreateStore(builder.CreateSub(shift_pre_value, ConstantInt::get(int_type_internal, 2), "shift_pre_value_upper"), shift_pre_ptr.value);
        builder.CreateStore(arg_value, arg_ptr);

        builder.CreateBr(check_big_arg);

    }


    // ----------------------------------------------------
    // Main loop initialisation
    {

        builder.SetInsertPoint(init_main);

        // Shift argument value to be return type
        arg_value = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_value");
        
        if (fxparg.scalarFracBitsAmt() < fxpret.scalarFracBitsAmt()) {
            builder.CreateStore(builder.CreateShl(arg_value, fxpret.scalarFracBitsAmt() - fxparg.scalarFracBitsAmt(), "ret_value_init"), return_value_ptr);
        }
        else
        {
            builder.CreateStore(builder.CreateAShr(arg_value, fxparg.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt(), "ret_value_init"), return_value_ptr);
        }

        Value *return_value = builder.CreateAlloca(int_type_ret, nullptr, "return_value");
        builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(return_value_ptr), return_value_ptr, "ret_value_init"), return_value);

        // Set the iterator to 1
        //auto one_value = builder.CreateLoad(getElementTypeFromValuePointer(one_ptr.value), one_ptr.value, "one");
        builder.CreateStore(ConstantInt::get(int_type_internal, 1), i_ptr.value);

        // Set the x and y values to arg + 0.25 and arg - 0.25 

        // x = arg + 0.25
        auto x_value = builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(return_value), return_value), builder.CreateLoad(getElementTypeFromValuePointer(quarter_ptr.value), quarter_ptr.value, "quarter_wide"), "x_value");
        builder.CreateStore(x_value, x_ptr.value);

        // y = arg - 0.25
        auto y_value = builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(return_value), return_value), builder.CreateLoad(getElementTypeFromValuePointer(quarter_ptr.value), quarter_ptr.value, "quarter_wide"), "y_value");
        builder.CreateStore(y_value, y_ptr.value);

        // Temp values to store updates
        // Value *x_update = builder.CreateAlloca(int_type_ret, nullptr, "x_update_value");
        // Value *y_update = builder.CreateAlloca(int_type_ret, nullptr, "y_update_value");
        // Value *k_value;
        
        // set k to 4
        //auto four_value = builder.CreateLoad(getElementTypeFromValuePointer(four_ptr.value), four_ptr.value, "four_narrow");
        builder.CreateStore(ConstantInt::get(int_type_internal, 4), k_ptr.value);

        builder.CreateBr(check_loop);

    }

    // ----------------------------------------------------

    {
        builder.SetInsertPoint(check_loop);

        LLVM_DEBUG(dbgs() << "Start loop"
                    << "\n");

        auto i_value = builder.CreateLoad(getElementTypeFromValuePointer(i_ptr.value), i_ptr.value, "i_value");

        // Check whether i < cordic_sqrt_total_iterations; if so, go to loop body. Else, go to the end of the function.
        Value *iIsLessThanN = builder.CreateICmpSLT(
            i_value,
            ConstantInt::get(int_type_internal, fxpret.scalarFracBitsAmt()), "loop_condition");
        
        builder.CreateCondBr(iIsLessThanN, loop_body,
                            end);

    }


    // Loop body
    {
        builder.SetInsertPoint(loop_body);

        // Current argument value
        // arg_value = builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_value_curr");
        // arg_value_wide = builder.CreateShl(builder.CreateSExt(arg_value, int_type_arg, "sign_extended_arg"), internal_fxpt.scalarFracBitsAmt() - fxparg.scalarFracBitsAmt(), "arg_value_wide_curr");

        // Current x and y values
        Value *x_value = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_curr");
        Value *y_value = builder.CreateLoad(getElementTypeFromValuePointer(y_ptr.value), y_ptr.value, "y_curr");

        // sign = y >= 0 ? -1 : 1;
        // Shift right until we get the most significant bit only
        Value *update_sign = builder.CreateSelect(
            builder.CreateICmpSGT(y_value, zero_value, "arg_is_positive"),
            ConstantInt::get(int_type_ret, -1), ConstantInt::get(int_type_ret, 1), "update_sign");

        // update_sign > 0 ?
        auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_value, "update_sign_greater_zero");

        LLVM_DEBUG(dbgs() << "Sign greater than zero set"
                        << "\n");

        //auto shift_value = builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(i_ptr.value), i_ptr.value), fxpret.scalarFracBitsAmt() - flttofix::cordic_sqrt_internal_width_fractional + 1, "shift_value");
        auto shift_value = builder.CreateLoad(getElementTypeFromValuePointer(i_ptr.value), i_ptr.value, "shift_value");
        
        Value *y_update = builder.CreateAShr(x_value, shift_value, "y_update");
        Value *x_update = builder.CreateAShr(y_value, shift_value, "x_update");

        y_value = builder.CreateSelect(
            update_sign_greater_zero, builder.CreateAdd(y_value, y_update, "y_update"), builder.CreateSub(y_value, y_update, "y_update"), "y_update_select");

        x_value = builder.CreateSelect(
            update_sign_greater_zero, builder.CreateAdd(x_value, x_update, "x_update"), builder.CreateSub(x_value, x_update, "x_update"), "x_update_select");

        builder.CreateStore(y_value, y_ptr.value);
        builder.CreateStore(x_value, x_ptr.value);

        Value *k_value = builder.CreateLoad(getElementTypeFromValuePointer(k_ptr.value), k_ptr.value, "k_value");
        Value *i_value = builder.CreateLoad(getElementTypeFromValuePointer(i_ptr.value), i_ptr.value, "i_value");

        Value *isIequalToK = builder.CreateICmpEQ(
            i_value,
            k_value, "loop_condition_k");

        builder.CreateCondBr(isIequalToK, repetition,
                            iteration);
        }

    // ----------------------------------------------------

    // Repetition block

    {

        builder.SetInsertPoint(repetition);

        Value *k_value = builder.CreateLoad(getElementTypeFromValuePointer(k_ptr.value), k_ptr.value, "k_value_repetition");

        // k = 3 * k + 1
        k_value = builder.CreateLoad(getElementTypeFromValuePointer(k_ptr.value), k_ptr.value, "k_value_repetition");
        k_value = builder.CreateAdd(builder.CreateShl(k_value, ConstantInt::get(int_type_internal, 1), "k_shifted"), k_value, "3_times_k");
        k_value = builder.CreateAdd(k_value, ConstantInt::get(int_type_internal, 1), "3_times_k_plus_1");
        builder.CreateStore(k_value, k_ptr.value);

        builder.CreateBr(loop_body);

    }

    // ----------------------------------------------------

    // Iteration block
    {

        builder.SetInsertPoint(iteration);

        Value *i_value = builder.CreateLoad(getElementTypeFromValuePointer(i_ptr.value), i_ptr.value, "i_value_iteration");

        // i = i + 1
        builder.CreateStore(builder.CreateAdd(i_value,
                                            ConstantInt::get(int_type_internal, 1), "i_plus_1"),
                            i_ptr.value);

        builder.CreateBr(check_loop);
    
    }

    // ----------------------------------------------------

    // End block

    builder.SetInsertPoint(end);

    LLVM_DEBUG(dbgs() << "Shift_pre: ");
    shift_pre_value->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    // shift shift_pre by 1
    //shift_pre_value = builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(shift_pre_ptr.value), shift_pre_ptr.value, "shift_pre_value_end"), ConstantInt::get(int_type_ret, 1), "shift_pre_value_end_shifted");
    shift_pre_value = builder.CreateLoad(getElementTypeFromValuePointer(shift_pre_ptr.value), shift_pre_ptr.value, "shift_pre_value_end");
    shift_pre_value = builder.CreateAShr(shift_pre_value, ConstantInt::get(int_type_ret, 1), "shift_pre_value_end_shifted");

    LLVM_DEBUG(dbgs() << "Shift_pre_shifted: ");
    shift_pre_value->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    Value* ShiftPreGreaterThanZero = builder.CreateICmpSGT(shift_pre_value, ConstantInt::get(int_type_ret, 0), "shift_pre_greater_than_zero");

    LLVM_DEBUG(dbgs() << "Shift_gt_0: ");
    ShiftPreGreaterThanZero->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    // Shift x left by shift_pre
    Value *x_value = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_value_end");

    // Multiply x by 1/An (which is the return value of the function compute_An)

    std::string function_name("llvm.udiv.fix.i");
    function_name.append(std::to_string(fxpret.scalarToLLVMType(cont)->getScalarSizeInBits()));

    Function *udiv = M->getFunction(function_name);
    if (udiv == nullptr) {
      std::vector<llvm::Type *> fun_arguments;
      fun_arguments.push_back(
          fxpret.scalarToLLVMType(cont)); // depends on your type
      fun_arguments.push_back(
          fxpret.scalarToLLVMType(cont)); // depends on your type
      fun_arguments.push_back(Type::getInt32Ty(cont));
      FunctionType *fun_type = FunctionType::get(
          fxpret.scalarToLLVMType(cont), fun_arguments, false);
      udiv = llvm::Function::Create(fun_type, GlobalValue::ExternalLinkage,
                                    function_name, M);
    }

    x_value = builder.CreateCall(
        udiv, {x_value, An_ptr.value,
               llvm::ConstantInt::get(fxpret.scalarToLLVMType(cont),
                                      fxpret.scalarFracBitsAmt())});

    builder.CreateStore(builder.CreateSelect(ShiftPreGreaterThanZero, 
                shift_pre_value, 
                builder.CreateSub(ConstantInt::get(int_type_internal, 0), shift_pre_value), 
                "shift_pre_select"), shift_pre_ptr.value);

    // auto shift = builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(shift_pre_ptr.value), shift_pre_ptr.value, "shift"), fxpret.scalarFracBitsAmt(), "shift");
    // shift = builder.CreateShl(shift, fxpret.scalarFracBitsAmt(), "shift");

    auto shift = builder.CreateLoad(getElementTypeFromValuePointer(shift_pre_ptr.value), shift_pre_ptr.value, "shift");

    auto x_true = builder.CreateLShr(x_value, shift, "x_shifted");
    auto x_false = builder.CreateShl(x_value, shift, "x_shifted"); 

    Value *return_value = builder.CreateSelect(ShiftPreGreaterThanZero,
                    x_true, 
                    x_false, 
                    "x_shifted_select");

    builder.CreateStore(return_value, return_value_ptr);


    builder.CreateBr(result);

    // ----------------------------------------------------
    {
        builder.SetInsertPoint(result);

        // Return the result
        Value *return_value = builder.CreateLoad(getElementTypeFromValuePointer(return_value_ptr), return_value_ptr, "return_value");
        builder.CreateRet(return_value);    

        return true;
    }
}


} // namespace flttofix
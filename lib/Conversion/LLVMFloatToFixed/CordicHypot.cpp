/*
    CORDIC for hypot
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

bool createHypot(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
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

    TaffoMath::getFixedFromRet(ref, oldf, fxpret, foundRet);
    TaffoMath::getFixedFromArg(ref, oldf, fxparg1, 0, foundArg1);
    TaffoMath::getFixedFromArg(ref, oldf, fxparg2, 1, foundArg2);

    if (!foundRet || !foundArg1 || !foundArg2) {
        LLVM_DEBUG(dbgs() << "Return or argument not found\n");
        return partialSpecialCall(newfs, foundRet, fxpret);
    }



    auto int_type_arg1 = fxparg1.scalarToLLVMType(cont);
    LLVM_DEBUG(dbgs() << "Argument fixed point type 1: ");
    int_type_arg1->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto int_type_arg2 = fxparg2.scalarToLLVMType(cont);
    LLVM_DEBUG(dbgs() << "Argument fixed point type 2: ");
    int_type_arg2->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    auto int_type_ret = fxpret.scalarToLLVMType(cont);
    LLVM_DEBUG(dbgs() << "Return fixed point type: ");
    int_type_ret->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    Value *arg1_ptr = builder.CreateAlloca(int_type_arg1, nullptr, "arg1");
    builder.CreateStore(newfs->getArg(0), arg1_ptr);
    Value *arg2_ptr = builder.CreateAlloca(int_type_arg2, nullptr, "arg2");
    builder.CreateStore(newfs->getArg(1), arg2_ptr);
    Value *result = builder.CreateAlloca(int_type_ret, nullptr, "result");


    LLVM_DEBUG(dbgs() << "arg_ptr: ");
    arg1_ptr->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    BasicBlock *body = BasicBlock::Create(cont, "Body", newfs);
    BasicBlock *return_point = BasicBlock::Create(cont, "Return", newfs);

    BasicBlock *checkArgIsPos = BasicBlock::Create(cont, "check_arg_is_pos", newfs);
    BasicBlock *argIsNotPos = BasicBlock::Create(cont, "arg_is_pos", newfs);

    builder.CreateBr(checkArgIsPos);
    {
    builder.SetInsertPoint(checkArgIsPos);

    Value *arg1 = builder.CreateLoad(int_type_arg1, arg1_ptr);
    Value *arg2 = builder.CreateLoad(int_type_arg2, arg2_ptr);

    Value *arg1_is_pos = builder.CreateICmpSGE(arg1, ConstantInt::get(int_type_arg1, 0), "arg1_is_zero");
    Value *arg2_is_pos = builder.CreateICmpSGE(arg2, ConstantInt::get(int_type_arg2, 0), "arg2_is_zero");

    builder.CreateCondBr(builder.CreateAnd(arg1_is_pos, arg2_is_pos), body, argIsNotPos);
    }
    builder.SetInsertPoint(argIsNotPos);

    builder.CreateStore(ConstantInt::get(int_type_ret, 0), result);
    builder.CreateBr(return_point);
    
    
    builder.SetInsertPoint(body);

    // Generate strings for constants names
    std::string S_arg1_point = "." + std::to_string(fxparg1.scalarFracBitsAmt());
    std::string S_arg2_point = "." + std::to_string(fxparg2.scalarFracBitsAmt());
    std::string S_ret_point = "." + std::to_string(fxpret.scalarFracBitsAmt());

    // Pointer to sqrt2m1
    TaffoMath::pair_ftp_value<llvm::Constant *> sqrt2m1(fxpret);
    // Ponter to intermediate
    TaffoMath::pair_ftp_value<llvm::Value *> intermediate(fxpret);
    intermediate.value = builder.CreateAlloca(int_type_ret, nullptr, "intermediate");

    bool sqrt2m1_created = TaffoMath::createFixedPointFromConst(
        cont, ref, flttofix::sqrt2m1, fxpret, sqrt2m1.value, sqrt2m1.fpt);

    if (!sqrt2m1_created) {
        LLVM_DEBUG(dbgs() << "Could not create sqrt2m1\n");
        return false;
    }

    sqrt2m1.value = TaffoMath::createGlobalConst(
        M, "sqrt2m1" + S_ret_point, sqrt2m1.fpt.scalarToLLVMType(cont), sqrt2m1.value,
        dataLayout.getPrefTypeAlignment(sqrt2m1.fpt.scalarToLLVMType(cont)));



    std::string function_name("llvm.umul.fix.i");
    function_name.append(std::to_string(fxpret.scalarToLLVMType(cont)->getScalarSizeInBits()));

    LLVM_DEBUG(dbgs() << "Function name: " << function_name << "\n");

    Function *umul = M->getFunction(function_name);
    if (umul == nullptr) {
        LLVM_DEBUG(dbgs() << "Creating function\n");
        std::vector<llvm::Type *> fun_arguments;
        fun_arguments.push_back(
            fxpret.scalarToLLVMType(cont)); // depends on your type
        fun_arguments.push_back(
            fxpret.scalarToLLVMType(cont)); // depends on your type
        fun_arguments.push_back(Type::getInt32Ty(cont));
        FunctionType *fun_type = FunctionType::get(
            fxpret.scalarToLLVMType(cont), fun_arguments, false);
        umul = llvm::Function::Create(fun_type, GlobalValue::ExternalLinkage,
                                        function_name, M);
    }

    Value* arg1 = builder.CreateLoad(int_type_arg1, arg1_ptr);
    Value* arg2 = builder.CreateLoad(int_type_arg2, arg2_ptr);
    Value* int1 = builder.CreateAlloca(int_type_ret, nullptr, "int1");
    Value* int2 = builder.CreateAlloca(int_type_ret, nullptr, "int2");

    if (fxparg1.scalarFracBitsAmt() < fxpret.scalarFracBitsAmt()) {
        builder.CreateStore(builder.CreateShl(arg1, fxpret.scalarFracBitsAmt() - fxparg1.scalarFracBitsAmt(), "ret_value_init"), int1);
    }
    else
    {
        builder.CreateStore(builder.CreateAShr(arg1, fxparg1.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt(), "ret_value_init"), int1);
    }

    if (fxparg2.scalarFracBitsAmt() < fxpret.scalarFracBitsAmt()) {
        builder.CreateStore(builder.CreateShl(arg2, fxpret.scalarFracBitsAmt() - fxparg2.scalarFracBitsAmt(), "ret_value_init"), int2);
    }
    else
    {
        builder.CreateStore(builder.CreateAShr(arg2, fxparg2.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt(), "ret_value_init"), int2);
    }


    auto aleb = builder.CreateICmpSLE(builder.CreateLoad(getElementTypeFromValuePointer(int1), int1), builder.CreateLoad(getElementTypeFromValuePointer(int2), int2), "aleb");


    Value* intermediate_val = builder.CreateSelect(aleb, int1, int2, "intermediate");
    Value* b = builder.CreateSelect(aleb, int2, int1, "b");

    Value* res = builder.CreateCall(
        umul, {builder.CreateLoad(getElementTypeFromValuePointer(intermediate_val), intermediate_val),
                    builder.CreateLoad(getElementTypeFromValuePointer(sqrt2m1.value), sqrt2m1.value),
               llvm::ConstantInt::get(fxpret.scalarToLLVMType(cont),
                                      fxpret.scalarFracBitsAmt())});
    builder.CreateStore(res, intermediate.value);

    builder.CreateStore(builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(intermediate.value), intermediate.value), 
                                        builder.CreateLoad(getElementTypeFromValuePointer(b), b), "result"), result);

    builder.CreateBr(return_point);
    builder.SetInsertPoint(return_point);

    builder.CreateRet(builder.CreateLoad(getElementTypeFromValuePointer(result), result));

    return true;

}


} // namespace flttofix
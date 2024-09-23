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

bool createExp(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf, const ExpFunType &funcType)
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

  LLVM_DEBUG(dbgs() << "fxparg: " << fxparg.scalarBitsAmt() << " frac part: " << fxparg.scalarFracBitsAmt() << " difference: " << fxparg.scalarBitsAmt() - fxparg.scalarFracBitsAmt() << "\n");

  LLVM_DEBUG(dbgs() << "The return type is signed? " << fxpret.scalarIsSigned() << "\n");
  LLVM_DEBUG(dbgs() << "The argument type is signed? " << fxparg.scalarIsSigned() << "\n");


  /*
    Define LLVM integer types that will hold our variables.

    In case the argument is positive we could the same data type for the arg and the internal variables, as they will end up at a similar magnitude.
    However, for negative arguments, the internal variables will have a much larger magnitude than the argument.

    The solution is to just use an intermediate fixed point type with a larger number of bits: we use 64 bits in total.
  */
  auto internal_fxpt = flttofix::FixedPointType(true, flttofix::cordic_exp_internal_width_fractional, flttofix::cordic_exp_internal_width);

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

  // If the argument is unsigned, make it signed
  if (!fxparg.scalarIsSigned()) {
    LLVM_DEBUG(dbgs() << "Argument is unsigned: shifting it to the right by 1 bit\n");
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), ConstantInt::get(int_type_narrow, 1), "arg_shifted_was_unsigned"), arg_ptr);
    fxparg.scalarFracBitsAmt() = fxparg.scalarFracBitsAmt() - 1;
    fxparg.scalarIsSigned() = true;
  }

  /*
    The largest constant we have to use is about 3.2. Internally, we use the argument's type; the problem is that if the argument's fixed point type has very few integer bits, we may not have enough to represent the various constants.
    Thus, we must make sure that we have at least 2 integer bits +1 for the sign; if we do need more, we must also shift the argument to the right.
  */
  if (fxparg.scalarIntegerBitsAmt() < 3) {
    LLVM_DEBUG(dbgs() << "Argument is too small: shifting argument to the right by " << 3 - fxparg.scalarIntegerBitsAmt() << " bit(s)\n");
    builder.CreateStore(builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), ConstantInt::get(int_type_narrow, 3 - fxparg.scalarIntegerBitsAmt()), "arg_shifted_was_too_small"), arg_ptr);
    fxparg.scalarFracBitsAmt() = fxparg.scalarBitsAmt() - 3;
    LLVM_DEBUG(dbgs() << "New argument fixed point type: " << fxparg << "\n");
  }

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

  // Pointer to minus one (for comparison with the argument)
  TaffoMath::pair_ftp_value<llvm::Constant *> minus_one_ptr_arg(fxparg);
  bool minus_one_ptr_arg_created = TaffoMath::createFixedPointFromConst(
      cont, ref, -1.0, fxparg, minus_one_ptr_arg.value, minus_one_ptr_arg.fpt);
  if (minus_one_ptr_arg_created)
    minus_one_ptr_arg.value = TaffoMath::createGlobalConst(
        M, "minus_one_ptr_arg" + S_arg_point, minus_one_ptr_arg.fpt.scalarToLLVMType(cont), minus_one_ptr_arg.value,
        dataLayout.getPrefTypeAlignment(minus_one_ptr_arg.fpt.scalarToLLVMType(cont)));

  // Pointer to one (for returning)
  TaffoMath::pair_ftp_value<llvm::Constant *> one_ptr_ret(fxpret);
  bool one_ptr_ret_created = TaffoMath::createFixedPointFromConst(
      cont, ref, 1.0, fxpret, one_ptr_ret.value, one_ptr_ret.fpt);
  if (one_ptr_ret_created)
    one_ptr_ret.value = TaffoMath::createGlobalConst(
        M, "one_ptr_ret" + S_arg_point, one_ptr_ret.fpt.scalarToLLVMType(cont), one_ptr_ret.value,
        dataLayout.getPrefTypeAlignment(one_ptr_ret.fpt.scalarToLLVMType(cont)));

  // Pointer to e (for returning)
  TaffoMath::pair_ftp_value<llvm::Constant *> e_ptr_arg(fxpret);
  bool e_ptr_arg_created = false;
  // Pointer to e^-1 (for returning)
  TaffoMath::pair_ftp_value<llvm::Constant *> e_inv_ptr_arg(fxpret);
  bool e_inv_ptr_arg_created = false;

  // Pointer to 2 (for returning)
  TaffoMath::pair_ftp_value<llvm::Constant *> two_ptr_arg(fxpret);
  bool two_ptr_arg_created = false;
  // Pointer to 2^-1 (for returning)
  TaffoMath::pair_ftp_value<llvm::Constant *> two_inv_ptr_arg(fxpret);
  bool two_inv_ptr_arg_created = false;

  // Pointer to e-1 (for returning)
  TaffoMath::pair_ftp_value<llvm::Constant *> e_minus_one_ptr_arg(fxpret);
  bool e_minus_one_ptr_arg_created = false;
  // Pointer to e^(-1)-1 (for returning)
  TaffoMath::pair_ftp_value<llvm::Constant *> e_inv_minus_one_ptr_arg(fxpret);
  bool e_inv_minus_one_ptr_arg_created = false;

  if (funcType == ExpFunType::Exp) {
    LLVM_DEBUG(dbgs() << "Creating exp constants\n");

    // Pointer to e (for returning)
    e_ptr_arg_created = TaffoMath::createFixedPointFromConst(
        cont, ref, flttofix::e, fxpret, e_ptr_arg.value, e_ptr_arg.fpt);
    if (e_ptr_arg_created)
      e_ptr_arg.value = TaffoMath::createGlobalConst(
          M, "e_ptr_arg" + S_arg_point, e_ptr_arg.fpt.scalarToLLVMType(cont), e_ptr_arg.value,
          dataLayout.getPrefTypeAlignment(e_ptr_arg.fpt.scalarToLLVMType(cont)));

    // Pointer to e^-1 (for returning)
    e_inv_ptr_arg_created = TaffoMath::createFixedPointFromConst(
        cont, ref, flttofix::e_inv, fxpret, e_inv_ptr_arg.value, e_inv_ptr_arg.fpt);
    if (e_inv_ptr_arg_created)
      e_inv_ptr_arg.value = TaffoMath::createGlobalConst(
          M, "e_inv_ptr_arg" + S_arg_point, e_inv_ptr_arg.fpt.scalarToLLVMType(cont), e_inv_ptr_arg.value,
          dataLayout.getPrefTypeAlignment(e_inv_ptr_arg.fpt.scalarToLLVMType(cont)));
  } else if (funcType == ExpFunType::Exp2) {
    LLVM_DEBUG(dbgs() << "Creating exp2 constants\n");

    // Pointer to 2 (for returning)
    two_ptr_arg_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 2.0, fxpret, two_ptr_arg.value, two_ptr_arg.fpt);
    if (two_ptr_arg_created)
      two_ptr_arg.value = TaffoMath::createGlobalConst(
          M, "two_ptr_arg" + S_arg_point, two_ptr_arg.fpt.scalarToLLVMType(cont), two_ptr_arg.value,
          dataLayout.getPrefTypeAlignment(two_ptr_arg.fpt.scalarToLLVMType(cont)));

    // Pointer to 2^-1 (for returning)
    two_inv_ptr_arg_created = TaffoMath::createFixedPointFromConst(
        cont, ref, 0.5, fxpret, two_inv_ptr_arg.value, two_inv_ptr_arg.fpt);
    if (two_inv_ptr_arg_created)
      two_inv_ptr_arg.value = TaffoMath::createGlobalConst(
          M, "two_inv_ptr_arg" + S_arg_point, two_inv_ptr_arg.fpt.scalarToLLVMType(cont), two_inv_ptr_arg.value,
          dataLayout.getPrefTypeAlignment(two_inv_ptr_arg.fpt.scalarToLLVMType(cont)));
  } else {
    LLVM_DEBUG(dbgs() << "Creating expm1 constants\n");

    // Pointer to e-1 (for returning)
    e_minus_one_ptr_arg_created = TaffoMath::createFixedPointFromConst(
        cont, ref, flttofix::e_minus_one, fxpret, e_minus_one_ptr_arg.value, e_minus_one_ptr_arg.fpt);
    if (e_minus_one_ptr_arg_created)
      e_minus_one_ptr_arg.value = TaffoMath::createGlobalConst(
          M, "e_minus_one_ptr_arg_created" + S_arg_point, e_minus_one_ptr_arg.fpt.scalarToLLVMType(cont), e_minus_one_ptr_arg.value,
          dataLayout.getPrefTypeAlignment(e_minus_one_ptr_arg.fpt.scalarToLLVMType(cont)));

    // Pointer to e^-1 (for returning)
    e_inv_minus_one_ptr_arg_created = TaffoMath::createFixedPointFromConst(
        cont, ref, flttofix::e_inv_minus_one, fxpret, e_inv_minus_one_ptr_arg.value, e_inv_minus_one_ptr_arg.fpt);
    if (e_inv_minus_one_ptr_arg_created)
      e_inv_minus_one_ptr_arg.value = TaffoMath::createGlobalConst(
          M, "e_inv_minus_one_ptr_arg_created" + S_arg_point, e_inv_minus_one_ptr_arg.fpt.scalarToLLVMType(cont), e_inv_minus_one_ptr_arg.value,
          dataLayout.getPrefTypeAlignment(e_inv_minus_one_ptr_arg.fpt.scalarToLLVMType(cont)));
  }

  LLVM_DEBUG(dbgs() << "Created special constants\n");


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

    Also! We must initialise some of these variables later since if their block never gets placed, we will get an error down the line
    since technically they are never terminated either.
    */

  BasicBlock *checkArgIsZero;
  BasicBlock *argIsZero;

  BasicBlock *checkArgIsOne_pre = BasicBlock::Create(cont, "check_arg_is_one_pre", newfs);
  BasicBlock *checkArgIsOne;
  BasicBlock *argIsOne;

  BasicBlock *checkArgIsMinusOne_pre = BasicBlock::Create(cont, "check_arg_is_minus_one_pre", newfs);
  BasicBlock *checkArgIsMinusOne;
  BasicBlock *argIsMinusOne;

  BasicBlock *init_pre = BasicBlock::Create(cont, "init_pre", newfs);

  // ----------------------------------------------------
  // Special cases: if we fall into one of these, we can return our special value directly
  // and skip the rest of the function.

  /*
Check whether we successfully created the constant; if not, we calculate the result at runtime.
From an IR perspective, we immediately jump to the next special case.
*/
  if (!(one_ptr_ret_created)) {
    LLVM_DEBUG(dbgs() << "WARNING: This section (checkArgIsZero) needs the return constant 1.0 but it was not created successfully.\n");
    builder.CreateBr(checkArgIsOne_pre);
  } else {
    LLVM_DEBUG(dbgs() << "Create checkArgIsZero"
                      << "\n");

    checkArgIsZero = BasicBlock::Create(cont, "check_arg_is_zero", newfs);

    builder.CreateBr(checkArgIsZero);
    builder.SetInsertPoint(checkArgIsZero);
    {
      // Arg == 0 -> return 1 in case of exp and exp2, 0 in case of expm1

      Value *check = builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_initial"),
                                          ConstantInt::get(int_type_narrow, 0), "arg_is_zero");

      argIsZero = BasicBlock::Create(cont, "arg_is_zero", newfs);

      builder.CreateCondBr(check, argIsZero, checkArgIsOne_pre);

      builder.SetInsertPoint(argIsZero);
      {
        // Copy the result to the return value
        if (funcType == ExpFunType::Exp) {
          builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(one_ptr_ret.value), one_ptr_ret.value), return_value_ptr);
        } else {
          builder.CreateStore(ConstantInt::get(int_type_narrow, 0), return_value_ptr);
        }

        builder.CreateBr(end);
      }
    }
  }

  builder.SetInsertPoint(checkArgIsOne_pre);

  /*
       Check whether we successfully created the constant; if not, we calculate the result at runtime.
       From an IR perspective, we immediately jump to the next special case.
      */
  if (!(one_ptr_arg_created) || (funcType == ExpFunType::Exp && !e_ptr_arg_created) || (funcType == ExpFunType::Exp2 && !two_ptr_arg_created) || (funcType == ExpFunType::Expm1 && !e_minus_one_ptr_arg_created)) {
    LLVM_DEBUG(dbgs() << "WARNING: This section (checkArgIsOne) needs: 1.0, 2.0 or e-1.0, but either one or more were not created successfully.\n");
    builder.CreateBr(checkArgIsMinusOne_pre);
  } else {
    LLVM_DEBUG(dbgs() << "Create checkArgIsOne"
                      << "\n");
    checkArgIsOne = BasicBlock::Create(cont, "check_arg_is_one", newfs);
    argIsOne = BasicBlock::Create(cont, "arg_is_one", newfs);

    builder.CreateBr(checkArgIsOne);
    builder.SetInsertPoint(checkArgIsOne);
    {
      // Arg == 1

      Value *check = builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_initial"),
                                          builder.CreateLoad(getElementTypeFromValuePointer(one_ptr_arg.value), one_ptr_arg.value, "constant_one_arg"), "arg_is_one");

      builder.CreateCondBr(check, argIsOne, checkArgIsMinusOne_pre);

      builder.SetInsertPoint(argIsOne);
      {
        // Copy the result to the return value
        if (funcType == ExpFunType::Exp) {
          builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(e_ptr_arg.value), e_ptr_arg.value), return_value_ptr);
        } else if (funcType == ExpFunType::Exp2) {
          builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(two_ptr_arg.value), two_ptr_arg.value), return_value_ptr);
        } else {
          builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(e_minus_one_ptr_arg.value), e_minus_one_ptr_arg.value), return_value_ptr);
        }

        builder.CreateBr(end);
      }
    }
  }

  builder.SetInsertPoint(checkArgIsMinusOne_pre);

  /*
     Check whether we successfully created the constant; if not, we calculate the result at runtime.
     From an IR perspective, we immediately jump to the next special case.
    */
  if (!(minus_one_ptr_arg_created) || (funcType == ExpFunType::Exp && !e_inv_ptr_arg_created) || (funcType == ExpFunType::Exp2 && !two_inv_ptr_arg_created) || (funcType == ExpFunType::Expm1 && !e_inv_minus_one_ptr_arg_created)) {
    LLVM_DEBUG(dbgs() << "WARNING: This section (checkArgIsMinusOne) needs: -1.0, 1/e, 1/2 or 1/(e-1), but either one or more were not created successfully.\n");
    builder.CreateBr(init_pre);
  } else {
    LLVM_DEBUG(dbgs() << "Create checkArgIsMinusOne"
                      << "\n");

    checkArgIsMinusOne = BasicBlock::Create(cont, "check_arg_is_minus_one", newfs);
    argIsMinusOne = BasicBlock::Create(cont, "arg_is_minus_one", newfs);

    builder.CreateBr(checkArgIsMinusOne);
    builder.SetInsertPoint(checkArgIsMinusOne);
    {
      // Arg = -1

      Value *check = builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_initial"),
                                          builder.CreateLoad(getElementTypeFromValuePointer(minus_one_ptr_arg.value), minus_one_ptr_arg.value, "constant_minus_one_arg"), "arg_is_minus_one");

      builder.CreateCondBr(check, argIsMinusOne, init_pre);

      builder.SetInsertPoint(argIsMinusOne);
      {
        // Copy the result to the return value
        if (funcType == ExpFunType::Exp) {
          builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(e_inv_ptr_arg.value), e_inv_ptr_arg.value), return_value_ptr);
        } else if (funcType == ExpFunType::Exp2) {
          builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(two_inv_ptr_arg.value), two_inv_ptr_arg.value), return_value_ptr);
        } else {
          builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(e_inv_minus_one_ptr_arg.value), e_inv_minus_one_ptr_arg.value), return_value_ptr);
        }

        builder.CreateBr(end);
      }
    }
  }

  builder.SetInsertPoint(init_pre);

  LLVM_DEBUG(dbgs() << "Create init"
                    << "\n");
  builder.CreateBr(init);
  builder.SetInsertPoint(init);

  // ----------------------------------------------------
  // Support variables that we use internally
  // The argument is created above

  // The two updaters that oscillate

  TaffoMath::pair_ftp_value<llvm::Value *> x_ptr(internal_fxpt);
  TaffoMath::pair_ftp_value<llvm::Value *> y_ptr(internal_fxpt);
  x_ptr.value = builder.CreateAlloca(int_type_wide, nullptr, "x");
  y_ptr.value = builder.CreateAlloca(int_type_wide, nullptr, "y");

  Value *output_temp;

  // Pointer to the current iteration counter
  Value *i_ptr = builder.CreateAlloca(int_type_narrow, nullptr, "i_ptr");
  // Pointer to zero in the internal (wide) fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_ptr_wide(internal_fxpt);
  // Pointer to zero in the return (narrow) fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_ptr_narrow(fxpret);
  // Pointer to An in the internal (wide) fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> An_ptr(internal_fxpt);
  // Pointer to An in the internal (wide) fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> ln2_ptr(fxparg);
  // Pointer to one in the internal (wide) fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> one_ptr_wide(internal_fxpt);
  // The arctanh array table
  TaffoMath::pair_ftp_value<llvm::Constant *,
                            TaffoMath::TABLELENGHT>
      arctanh_2power;

  // ----------------------------------------------------

  LLVM_DEBUG(dbgs() << "Initialising variables. 1/An_ptr=" << flttofix::compute_An_inv(flttofix::cordic_exp_negative_iterations, flttofix::cordic_exp_positive_iterations)
                    << "\n");

  bool zero_ptr_wide_created = TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, internal_fxpt, zero_ptr_wide.value, zero_ptr_wide.fpt);
  bool zero_ptr_narrow_created = TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, fxpret, zero_ptr_narrow.value, zero_ptr_narrow.fpt);
  bool An_ptr_created = TaffoMath::createFixedPointFromConst(
      cont, ref, flttofix::compute_An_inv(flttofix::cordic_exp_negative_iterations, flttofix::cordic_exp_positive_iterations), internal_fxpt, An_ptr.value, An_ptr.fpt);
  bool ln2_ptr_created = TaffoMath::createFixedPointFromConst(
      cont, ref, flttofix::ln2, fxparg, ln2_ptr.value, ln2_ptr.fpt);
  bool one_ptr_wide_created = TaffoMath::createFixedPointFromConst(
      cont, ref, 1.0, internal_fxpt, one_ptr_wide.value, one_ptr_wide.fpt);

  if (!(zero_ptr_wide_created && zero_ptr_narrow_created && An_ptr_created)) {
    LLVM_DEBUG(dbgs() << "===== ERROR: Could not create one or more of the initialisation constants\n");
    llvm_unreachable("Could not create one or more of the initialisation constants. Exp cannot continue.");
    return false;
  }

  if (funcType == ExpFunType::Exp2 && !ln2_ptr_created) {
    LLVM_DEBUG(dbgs() << "===== ERROR: Could not create ln2 constant\n");
    llvm_unreachable("Could not create ln2 constant. Exp2 cannot continue.");
    return false;
  }

  if (funcType == ExpFunType::Expm1 && !one_ptr_wide_created) {
    LLVM_DEBUG(dbgs() << "===== ERROR: Could not create one constant\n");
    llvm_unreachable("Could not create one constant. Expm1 cannot continue.");
    return false;
  }

  zero_ptr_wide.value = TaffoMath::createGlobalConst(
      M, "zero_ptr_wide" + S_int_point, zero_ptr_wide.fpt.scalarToLLVMType(cont), zero_ptr_wide.value,
      dataLayout.getPrefTypeAlignment(zero_ptr_wide.fpt.scalarToLLVMType(cont)));

  zero_ptr_narrow.value = TaffoMath::createGlobalConst(
      M, "zero_ptr_narrow" + S_ret_point, zero_ptr_narrow.fpt.scalarToLLVMType(cont), zero_ptr_narrow.value,
      dataLayout.getPrefTypeAlignment(zero_ptr_narrow.fpt.scalarToLLVMType(cont)));

  An_ptr.value = TaffoMath::createGlobalConst(
      M, "An_ptr" + S_int_point, An_ptr.fpt.scalarToLLVMType(cont), An_ptr.value,
      dataLayout.getPrefTypeAlignment(An_ptr.fpt.scalarToLLVMType(cont)));

  ln2_ptr.value = TaffoMath::createGlobalConst(
      M, "ln2_ptr" + S_arg_point, ln2_ptr.fpt.scalarToLLVMType(cont), ln2_ptr.value,
      dataLayout.getPrefTypeAlignment(ln2_ptr.fpt.scalarToLLVMType(cont)));

  one_ptr_wide.value = TaffoMath::createGlobalConst(
      M, "one_ptr_wide" + S_int_point, one_ptr_wide.fpt.scalarToLLVMType(cont), one_ptr_wide.value,
      dataLayout.getPrefTypeAlignment(one_ptr_wide.fpt.scalarToLLVMType(cont)));

  // ----------------------------------------------------
  // Create the table for arctanh

  LLVM_DEBUG(dbgs() << "===== Create arctanh table ====="
                    << "\n");

  llvm::AllocaInst *pointer_to_arctanh_array = nullptr;

  for (int i = 0; i < TaffoMath::TABLELENGHT; i++) {
    LLVM_DEBUG(dbgs() << "Element " << i << ":\n");
    arctanh_2power.fpt.push_back(flttofix::FixedPointType(fxparg));
    Constant *tmp = nullptr;
    auto &current_fpt = arctanh_2power.fpt.front();
    bool this_value_created = TaffoMath::createFixedPointFromConst(
        cont, ref, flttofix::arctanh_2power[i], fxparg, tmp, current_fpt);

    if (!this_value_created) {
      LLVM_DEBUG(dbgs() << "===== ERROR: Could not create one the " << i << "th element of the arctanh table\n");
      std::string err_msg = "Could not create one the " + std::to_string(i) + "th element of the arctanh table. Exp cannot continue.";
      llvm_unreachable(err_msg.c_str());
      return false;
    }

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

  // ----------------------------------------------------
  // Create the multiplication function that is needed for the exp2 case.

  std::string mul_function_name("llvm.smul.fix.i");
  mul_function_name.append(std::to_string(fxparg.scalarToLLVMType(cont)->getScalarSizeInBits()));

  Function *function_mul;

  if (funcType == ExpFunType::Exp2) {
    function_mul = M->getFunction(mul_function_name);

    if (function_mul == nullptr) {
      std::vector<llvm::Type *> fun_arguments;
      fun_arguments.push_back(
          fxparg.scalarToLLVMType(cont));
      fun_arguments.push_back(
          fxparg.scalarToLLVMType(cont));
      fun_arguments.push_back(Type::getInt32Ty(cont));
      FunctionType *fun_type = FunctionType::get(
          fxparg.scalarToLLVMType(cont), fun_arguments, false);
      function_mul = llvm::Function::Create(fun_type, GlobalValue::ExternalLinkage,
                                            mul_function_name, M);
    }

    LLVM_DEBUG(dbgs() << "Mul function: ");
    function_mul->print(dbgs());
    LLVM_DEBUG(dbgs() << "\n");
  }

  // calculate exp

  LLVM_DEBUG(dbgs() << "Starting exp routine"
                    << "\n");

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

  auto An_value = builder.CreateLoad(getElementTypeFromValuePointer(An_ptr.value), An_ptr.value, "An_value");
  // Initialise x and y to the initial constant (which depends on the amount of iterations we do)
  if (funcType == ExpFunType::Exp2) {
    // x=An
    builder.CreateStore(An_value, x_ptr.value);
    // y=0
    builder.CreateStore(zero_value_wide, y_ptr.value);
    // Additionally, the argument should be equal to arg*ln2
    auto new_arg = builder.CreateCall(
        function_mul, {builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "initial_arg"), builder.CreateLoad(getElementTypeFromValuePointer(ln2_ptr.value), ln2_ptr.value, "ln2"),
                       llvm::ConstantInt::get(fxparg.scalarToLLVMType(cont),
                                              fxparg.scalarFracBitsAmt())});

    LLVM_DEBUG(dbgs() << "new_arg: ");
    new_arg->print(dbgs());
    LLVM_DEBUG(dbgs() << "\n");

    builder.CreateStore(new_arg, arg_ptr);
  } else {
    // x=An
    builder.CreateStore(An_value, x_ptr.value);
    // y=An
    builder.CreateStore(An_value, y_ptr.value);
  }

  LLVM_DEBUG(dbgs() << "Initial x and y set"
                    << "\n");

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
      ConstantInt::get(int_type_narrow, flttofix::cordic_exp_negative_iterations), "loop_condition_negatives");

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
    // Shift right until we get the most significant bit only
    Value *update_sign = builder.CreateSelect(
        builder.CreateICmpSGT(arg_value_wide, zero_value_wide, "arg_is_positive_loop1"),
        ConstantInt::get(int_type_wide, 1), ConstantInt::get(int_type_wide, -1), "update_sign_loop1");

    // update_sign > 0 ?
    auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_value_wide, "update_sign_greater_zero_loop1");

    // sign = arg >= 0 ? 1 : -1;
    Value *update_sign_narrow = builder.CreateSelect(
        builder.CreateICmpSGT(arg_value_narrow, zero_value_narrow, "arg_is_positive_narrow_loop1"),
        ConstantInt::get(int_type_narrow, 1), ConstantInt::get(int_type_narrow, -1), "update_sign_narrow_loop1");
    // update_sign > 0 ?
    auto update_sign_greater_zero_narrow = builder.CreateICmpSGT(update_sign_narrow, zero_value_narrow, "update_sign_greater_zero_narrow_loop1");

    LLVM_DEBUG(dbgs() << "Sign greater than zero set"
                      << "\n");

    /*
      shift_amt = cordic_exp_negative_iterations+2-i (casted to larger type since otherwise LLVM will complain)
      The original loop should compute 2^(-i+2), with i going from -m to 0. However our i starts from 0,
        so we need to compute 2^(i+2) instead and then shift right later.
     */
    Value *shift_amt = builder.CreateSub(
        ConstantInt::get(int_type_wide, flttofix::cordic_exp_negative_iterations + 2), i_value_wide, "shift_amt_loop1");

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
          update_sign_greater_zero, y_update, builder.CreateSub(zero_value_wide, y_update, "minus_y_upd_2_loop1"), "y_upd_3_loop1");

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
          update_sign_greater_zero, x_update, builder.CreateSub(zero_value_wide, x_update, "minus_x_upd_2_loop1"), "x_upd_3_loop1");

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

  i_value = builder.CreateLoad(getElementTypeFromValuePointer(i_ptr), i_ptr, "i_value_loop2");
  i_value_wide = builder.CreateZExt(
      i_value, int_type_wide, "i_value_wide_loop2");

  // Check whether i < (m+n); if so, go to loop body. Else, go to positive loop.
  Value *iIsLessThanN = builder.CreateICmpSLT(
      i_value,
      ConstantInt::get(int_type_narrow, flttofix::cordic_exp_total_iterations), "loop_condition_positives");

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
    // Shift right until we get the most significant bit only
    Value *update_sign = builder.CreateSelect(
        builder.CreateICmpSGT(arg_value_wide, zero_value_wide, "arg_is_positive_loop2"),
        ConstantInt::get(int_type_wide, 1), ConstantInt::get(int_type_wide, -1), "update_sign_loop2");

    // update_sign > 0 ?
    auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_value_wide, "update_sign_greater_zero_loop2");

    // sign = arg >= 0 ? 1 : -1;
    Value *update_sign_narrow = builder.CreateSelect(
        builder.CreateICmpSGT(arg_value_narrow, zero_value_narrow, "arg_is_positive_narrow_loop2"),
        ConstantInt::get(int_type_narrow, 1), ConstantInt::get(int_type_narrow, -1), "update_sign_narrow_loop2");
    // update_sign > 0 ?
    auto update_sign_greater_zero_narrow = builder.CreateICmpSGT(update_sign_narrow, zero_value_narrow, "update_sign_greater_zero_narrow_loop2");

    // shift_amt = i-m since we do not reset i (again, casted to larger type since otherwise LLVM will complain)
    Value *shift_amt = builder.CreateSub(i_value_wide,
                                         ConstantInt::get(int_type_wide, flttofix::cordic_exp_negative_iterations), "shift_amt_loop2");

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
          update_sign_greater_zero, y_update, builder.CreateSub(zero_value_wide, y_update, "minus_y_upd_1_loop2"), "y_upd_2_loop2");

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
          update_sign_greater_zero, x_update, builder.CreateSub(zero_value_wide, x_update, "minus_x_upd_1_loop2"), "x_upd_2_loop2");

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

  LLVM_DEBUG(dbgs() << "End of exp routine"
                    << "\n");

  LLVM_DEBUG(dbgs() << "x_ptr.value before shift: ");
  x_ptr.value->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // At this point x and y should both be equal to the result of the CORDIC algorithm. We return x.
  // If we are calculating exp2, we need to return x+y.
  // The trick we do is to simply check whether we are calculating exp2 and if so, we add x and y together, then store the result into x.

  if (funcType == ExpFunType::Exp2) {
    auto ret_x = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_value_final_exp2");
    auto ret_y = builder.CreateLoad(getElementTypeFromValuePointer(y_ptr.value), y_ptr.value, "y_value_final_exp2");
    Value *x_plus_y = builder.CreateAdd(ret_x, ret_y, "x_plus_y");
    builder.CreateStore(x_plus_y, x_ptr.value);
  }

  // If we are calculating expm1, we need to subtract 1 from the result. We use the same trick.
  if (funcType == ExpFunType::Expm1) {
    auto ret_x = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_value_final_expm1");
    auto one_value = builder.CreateLoad(getElementTypeFromValuePointer(one_ptr_wide.value), one_ptr_wide.value, "one_value");
    Value *x_minus_one = builder.CreateSub(ret_x, one_value, "x_minus_one");
    builder.CreateStore(x_minus_one, x_ptr.value);
  }

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
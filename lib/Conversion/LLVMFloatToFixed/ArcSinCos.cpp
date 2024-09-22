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


void print_fixp(Module *M, IRBuilder<> &builder, const char *c_str, Value *to_print, int comma)
{
  auto &cont = M->getContext();
  Value *generic =
      builder.CreateSIToFP(to_print, Type::getDoubleTy(cont));
  generic = builder.CreateFDiv(
      generic, ConstantFP::get(Type::getDoubleTy(cont), pow(2, comma)));
  Value *str = builder.CreateGlobalStringPtr(c_str);
  Function *fun = M->getFunction("printf");
  if (fun == 0) {
    std::vector<Type *> fun_arguments;
    fun_arguments.push_back(Type::getInt8PtrTy(cont)); // depends on your type
    FunctionType *fun_type =
        FunctionType::get(Type::getInt32Ty(cont), fun_arguments, true);
    fun = llvm::Function::Create(fun_type, GlobalValue::ExternalLinkage,
                                 "printf", M);
  }
  builder.CreateCall(fun, {str, generic});
}

bool createACos(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  newfs->deleteBody();
  Value *generic;
  Module *M = oldf->getParent();
  // retrive context used in later instruction
  llvm::LLVMContext &cont(oldf->getContext());
  DataLayout dataLayout(M);
  // get first basick block of function
  BasicBlock::Create(cont, "Entry", newfs);
  BasicBlock *where = &(newfs->getEntryBlock());
  IRBuilder<> builder(where, where->getFirstInsertionPt());
  // get return type fixed point
  flttofix::FixedPointType fxpret;
  flttofix::FixedPointType fxparg;
  bool foundRet = false;
  bool foundArg = false;
  int arg_size = (int)newfs->getArg(0)->getType()->getPrimitiveSizeInBits();
  Type *arg_type = newfs->getArg(0)->getType();
  Type *ret_type = newfs->getReturnType();
  assert(arg_type->getTypeID() == ret_type->getTypeID() && "mismatch type");
  TaffoMath::getFixedFromRet(ref, oldf, fxpret, foundRet);
  // get argument fixed point
  TaffoMath::getFixedFromArg(ref, oldf, fxparg, 0, foundArg);
  if (!foundRet || !foundArg) {
    return partialSpecialCall(newfs, foundRet, fxpret);
  }
  // create variable
  TaffoMath::pair_ftp_value<llvm::Value *> x(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Value *> y(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Value *> theta(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Value *> t(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Value *> x1(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Value *> y1(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Value *> d(
      FixedPointType(true, arg_size - 3, arg_size));

  // const
  TaffoMath::pair_ftp_value<llvm::Constant *> one(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Constant *> minus(
      FixedPointType(true, arg_size - 3, arg_size));

  // assign constant
  auto zero = ConstantInt::get(Type::getInt32Ty(cont), 0);
  TaffoMath::createFixedPointFromConst(
      cont, ref, 1, x.fpt, one.value, one.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, -1, x.fpt, minus.value, minus.fpt);

  // alloca variable
  x.value = builder.CreateAlloca(arg_type, nullptr, "x");
  y.value = builder.CreateAlloca(arg_type, nullptr, "y");
  theta.value = builder.CreateAlloca(arg_type, nullptr, "theta");
  t.value = builder.CreateAlloca(arg_type, nullptr, "t");
  x1.value = builder.CreateAlloca(arg_type, nullptr, "x1");
  y1.value = builder.CreateAlloca(arg_type, nullptr, "y1");
  d.value = builder.CreateAlloca(arg_type, nullptr, "d");


  // create arctan
  LLVM_DEBUG(dbgs() << "Create arctan table"
                    << "\n");
  TaffoMath::pair_ftp_value<llvm::Constant *, TaffoMath::TABLELENGHT> arctan_2power;

  for (int i = 0; i < TaffoMath::TABLELENGHT; i++) {
    arctan_2power.fpt.push_back(flttofix::FixedPointType(fxpret));
    Constant *tmp = nullptr;
    auto &current_fpt = arctan_2power.fpt.front();
    TaffoMath::createFixedPointFromConst(cont, ref,
                                         TaffoMath::arctan_2power[i],
                                         theta.fpt, tmp, current_fpt);
    arctan_2power.value.push_back(tmp);
    LLVM_DEBUG(dbgs() << i << ")");
  }

  auto arctanArrayType = llvm::ArrayType::get(
      arctan_2power.value[0]->getType(), TaffoMath::TABLELENGHT);

  LLVM_DEBUG(dbgs() << "ArrayType  " << arctanArrayType << "\n");
  auto arctanConstArray = llvm::ConstantArray::get(
      arctanArrayType, llvm::ArrayRef<llvm::Constant *>(arctan_2power.value));
  LLVM_DEBUG(dbgs() << "ConstantDataArray tmp2 " << arctanConstArray << "\n");
  auto alignement_arctan =
      dataLayout.getPrefTypeAlignment(arctan_2power.value[0]->getType());
  auto arctan_g = TaffoMath::createGlobalConst(
      M, "arctan_g." + std::to_string(theta.fpt.scalarFracBitsAmt()),
      arctanArrayType, arctanConstArray, alignement_arctan);

  auto loop_entry = BasicBlock::Create(cont, "Loop entry", newfs);
  auto cordic_body = BasicBlock::Create(cont, "cordic body", newfs);
  auto end_loop = BasicBlock::Create(cont, "end", newfs);
  auto i = builder.CreateAlloca(Type::getInt32Ty(cont), nullptr, "i");
  builder.CreateStore(zero, i);


  // set up value

  builder.CreateStore(zero, y.value);
  builder.CreateStore(zero, theta.value);
  builder.CreateStore(one.value, x.value);
  if (fxparg.scalarFracBitsAmt() > arg_size - 3) {
    builder.CreateStore(builder.CreateAShr(newfs->getArg(0), fxparg.scalarFracBitsAmt() - arg_size + 3), t.value);
  } else if (fxparg.scalarFracBitsAmt() < arg_size - 3) {
    builder.CreateStore(builder.CreateShl(newfs->getArg(0), -fxparg.scalarFracBitsAmt() + arg_size - 3), t.value);
  } else {
    builder.CreateStore(newfs->getArg(0), t.value);
  }
  builder.CreateBr(loop_entry);
  // end entry

  // begin loop entry
  builder.SetInsertPoint(loop_entry);
  generic = builder.CreateICmpSLT(builder.CreateLoad(getElementTypeFromValuePointer(i), i), ConstantInt::get(Type::getInt32Ty(cont), arg_size / 2));
  builder.CreateCondBr(generic, cordic_body, end_loop);

  builder.SetInsertPoint(cordic_body);

  // y>0
  generic = builder.CreateICmpSGE(builder.CreateLoad(getElementTypeFromValuePointer(y.value), y.value), zero);

  // d = 1 if x >= t else -1
  builder.CreateStore(builder.CreateSelect(
                          builder.CreateICmpSGE(builder.CreateLoad(getElementTypeFromValuePointer(x.value), x.value), builder.CreateLoad(getElementTypeFromValuePointer(t.value), t.value)),
                          builder.CreateSelect(generic, one.value, zero),
                          builder.CreateSelect(generic, zero, one.value)),
                      d.value);


  // theta = theta + 2*d*math.atan(math.pow(2,-i))
  auto tmp = builder.CreateGEP(getElementTypeFromValuePointer(arctan_g), arctan_g, {zero, builder.CreateLoad(getElementTypeFromValuePointer(i), i)});
  generic = builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(tmp), tmp), ConstantInt::get(Type::getInt32Ty(cont), 1));
  generic = builder.CreateSelect(builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(d.value), d.value), zero), builder.CreateSub(zero, generic), generic);
  builder.CreateStore(builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(theta.value), theta.value), generic), theta.value);


  //    t = t + t*math.pow(2,-2*i)
  generic = builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(i), i), ConstantInt::get(Type::getInt32Ty(cont), 1));
  builder.CreateStore(
      builder.CreateAdd(
          builder.CreateLoad(getElementTypeFromValuePointer(t.value), t.value),
          builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(t.value), t.value), generic)),
      t.value);


  //    x1= x-d*math.pow(2,-i)*y
  generic = builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(y.value), y.value), builder.CreateLoad(getElementTypeFromValuePointer(i), i));
  builder.CreateStore(
      builder.CreateSelect(
          builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(d.value), d.value), zero),
          builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(x.value), x.value), generic),
          builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(x.value), x.value), generic)),
      x1.value);


  // y1= d*math.pow(2,-i)*x + y
  generic = builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(x.value), x.value), builder.CreateLoad(getElementTypeFromValuePointer(i), i));
  builder.CreateStore(
      builder.CreateSelect(
          builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(d.value), d.value), zero),
          builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(y.value), y.value), generic),
          builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(y.value), y.value), generic)),
      y1.value);


  //    x= x1-d*math.pow(2,-i)*y1
  generic = builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(y1.value), y1.value), builder.CreateLoad(getElementTypeFromValuePointer(i), i));
  builder.CreateStore(
      builder.CreateSelect(
          builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(d.value), d.value), zero),
          builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(x1.value), x1.value), generic),
          builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(x1.value), x1.value), generic)),
      x.value);

  // y= d*math.pow(2,-i)*x1 + y1
  generic = builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(x1.value), x1.value), builder.CreateLoad(getElementTypeFromValuePointer(i), i));
  builder.CreateStore(
      builder.CreateSelect(
          builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(d.value), d.value), zero),
          builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(y1.value), y1.value), generic),
          builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(y1.value), y1.value), generic)),
      y.value);

  builder.CreateStore(builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(i), i), ConstantInt::get(Type::getInt32Ty(cont), 1)), i);

  builder.CreateBr(loop_entry);

  builder.SetInsertPoint(end_loop);

  if (fxpret.scalarFracBitsAmt() > arg_size - 3) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(theta.value), theta.value), fxpret.scalarFracBitsAmt() - arg_size + 3), theta.value);
  } else if (fxpret.scalarFracBitsAmt() < arg_size - 3) {
    builder.CreateStore(builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(theta.value), theta.value), -fxpret.scalarFracBitsAmt() + arg_size - 3), theta.value);
  }
  builder.CreateRet(builder.CreateLoad(getElementTypeFromValuePointer(theta.value), theta.value));

  return true;
}


bool createASin(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  newfs->deleteBody();
  Value *generic;
  Module *M = oldf->getParent();
  // retrive context used in later instruction
  llvm::LLVMContext &cont(oldf->getContext());
  DataLayout dataLayout(M);
  // get first basick block of function
  BasicBlock::Create(cont, "Entry", newfs);
  BasicBlock *where = &(newfs->getEntryBlock());
  IRBuilder<> builder(where, where->getFirstInsertionPt());
  // get return type fixed point
  flttofix::FixedPointType fxpret;
  flttofix::FixedPointType fxparg;
  bool foundRet = false;
  bool foundArg = false;
  int arg_size = (int)newfs->getArg(0)->getType()->getPrimitiveSizeInBits();
  Type *arg_type = newfs->getArg(0)->getType();
  Type *ret_type = newfs->getReturnType();
  assert(arg_type->getTypeID() == ret_type->getTypeID() && "mismatch type");
  TaffoMath::getFixedFromRet(ref, oldf, fxpret, foundRet);
  // get argument fixed point
  TaffoMath::getFixedFromArg(ref, oldf, fxparg, 0, foundArg);
  if (!foundRet || !foundArg) {
    return partialSpecialCall(newfs, foundRet, fxpret);
  }
  // create variable
  TaffoMath::pair_ftp_value<llvm::Value *> x(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Value *> y(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Value *> theta(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Value *> t(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Value *> x1(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Value *> y1(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Value *> d(
      FixedPointType(true, arg_size - 3, arg_size));

  // const
  TaffoMath::pair_ftp_value<llvm::Constant *> one(
      FixedPointType(true, arg_size - 3, arg_size));
  TaffoMath::pair_ftp_value<llvm::Constant *> minus(
      FixedPointType(true, arg_size - 3, arg_size));

  // assign constant
  auto zero = ConstantInt::get(Type::getInt32Ty(cont), 0);
  TaffoMath::createFixedPointFromConst(
      cont, ref, 1, x.fpt, one.value, one.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, -1, x.fpt, minus.value, minus.fpt);

  // alloca variable
  x.value = builder.CreateAlloca(arg_type, nullptr, "x");
  y.value = builder.CreateAlloca(arg_type, nullptr, "y");
  theta.value = builder.CreateAlloca(arg_type, nullptr, "theta");
  t.value = builder.CreateAlloca(arg_type, nullptr, "t");
  x1.value = builder.CreateAlloca(arg_type, nullptr, "x1");
  y1.value = builder.CreateAlloca(arg_type, nullptr, "y1");
  d.value = builder.CreateAlloca(arg_type, nullptr, "d");


  // create arctan
  LLVM_DEBUG(dbgs() << "Create arctan table"
                    << "\n");
  TaffoMath::pair_ftp_value<llvm::Constant *, TaffoMath::TABLELENGHT> arctan_2power;

  for (int i = 0; i < TaffoMath::TABLELENGHT; i++) {
    arctan_2power.fpt.push_back(flttofix::FixedPointType(fxpret));
    Constant *tmp = nullptr;
    auto &current_fpt = arctan_2power.fpt.front();
    TaffoMath::createFixedPointFromConst(cont, ref,
                                         TaffoMath::arctan_2power[i],
                                         theta.fpt, tmp, current_fpt);
    arctan_2power.value.push_back(tmp);
    LLVM_DEBUG(dbgs() << i << ")");
  }

  auto arctanArrayType = llvm::ArrayType::get(
      arctan_2power.value[0]->getType(), TaffoMath::TABLELENGHT);

  LLVM_DEBUG(dbgs() << "ArrayType  " << arctanArrayType << "\n");
  auto arctanConstArray = llvm::ConstantArray::get(
      arctanArrayType, llvm::ArrayRef<llvm::Constant *>(arctan_2power.value));
  LLVM_DEBUG(dbgs() << "ConstantDataArray tmp2 " << arctanConstArray << "\n");
  auto alignement_arctan =
      dataLayout.getPrefTypeAlignment(arctan_2power.value[0]->getType());
  auto arctan_g = TaffoMath::createGlobalConst(
      M, "arctan_g." + std::to_string(theta.fpt.scalarFracBitsAmt()),
      arctanArrayType, arctanConstArray, alignement_arctan);

  auto loop_entry = BasicBlock::Create(cont, "Loop entry", newfs);
  auto cordic_body = BasicBlock::Create(cont, "cordic body", newfs);
  auto end_loop = BasicBlock::Create(cont, "end", newfs);
  auto i = builder.CreateAlloca(Type::getInt32Ty(cont), nullptr, "i");
  builder.CreateStore(zero, i);


  // set up value

  builder.CreateStore(zero, y.value);
  builder.CreateStore(zero, theta.value);
  builder.CreateStore(one.value, x.value);
  if (fxparg.scalarFracBitsAmt() > arg_size - 3) {
    builder.CreateStore(builder.CreateAShr(newfs->getArg(0), fxparg.scalarFracBitsAmt() - arg_size + 3), t.value);
  } else if (fxparg.scalarFracBitsAmt() < arg_size - 3) {
    builder.CreateStore(builder.CreateShl(newfs->getArg(0), -fxparg.scalarFracBitsAmt() + arg_size - 3), t.value);
  } else {
    builder.CreateStore(newfs->getArg(0), t.value);
  }
  builder.CreateBr(loop_entry);
  // end entry

  // begin loop entry
  builder.SetInsertPoint(loop_entry);
  generic = builder.CreateICmpSLT(builder.CreateLoad(getElementTypeFromValuePointer(i), i), ConstantInt::get(Type::getInt32Ty(cont), arg_size / 2));
  builder.CreateCondBr(generic, cordic_body, end_loop);

  builder.SetInsertPoint(cordic_body);

  // x>0
  generic = builder.CreateICmpSGE(builder.CreateLoad(getElementTypeFromValuePointer(x.value), x.value), zero);

  // d = 1 if x >= t else -1
  builder.CreateStore(builder.CreateSelect(
                          builder.CreateICmpSGE(builder.CreateLoad(getElementTypeFromValuePointer(t.value), t.value), builder.CreateLoad(getElementTypeFromValuePointer(y.value), y.value)),
                          builder.CreateSelect(generic, one.value, zero),
                          builder.CreateSelect(generic, zero, one.value)),
                      d.value);


  // theta = theta + 2*d*math.atan(math.pow(2,-i))
  auto tmp = builder.CreateGEP(getElementTypeFromValuePointer(arctan_g), arctan_g, {zero, builder.CreateLoad(getElementTypeFromValuePointer(i), i)});
  generic = builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(tmp), tmp), ConstantInt::get(Type::getInt32Ty(cont), 1));
  generic = builder.CreateSelect(builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(d.value), d.value), zero), builder.CreateSub(zero, generic), generic);
  builder.CreateStore(builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(theta.value), theta.value), generic), theta.value);


  //    t = t + t*math.pow(2,-2*i)
  generic = builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(i), i), ConstantInt::get(Type::getInt32Ty(cont), 1));
  builder.CreateStore(
      builder.CreateAdd(
          builder.CreateLoad(getElementTypeFromValuePointer(t.value), t.value),
          builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(t.value), t.value), generic)),
      t.value);


  //    x1= x-d*math.pow(2,-i)*y
  generic = builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(y.value), y.value), builder.CreateLoad(getElementTypeFromValuePointer(i), i));
  builder.CreateStore(
      builder.CreateSelect(
          builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(d.value), d.value), zero),
          builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(x.value), x.value), generic),
          builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(x.value), x.value), generic)),
      x1.value);


  // y1= d*math.pow(2,-i)*x + y
  generic = builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(x.value), x.value), builder.CreateLoad(getElementTypeFromValuePointer(i), i));
  builder.CreateStore(
      builder.CreateSelect(
          builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(d.value), d.value), zero),
          builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(y.value), y.value), generic),
          builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(y.value), y.value), generic)),
      y1.value);


  //    x= x1-d*math.pow(2,-i)*y1
  generic = builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(y1.value), y1.value), builder.CreateLoad(getElementTypeFromValuePointer(i), i));
  builder.CreateStore(
      builder.CreateSelect(
          builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(d.value), d.value), zero),
          builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(x1.value), x1.value), generic),
          builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(x1.value), x1.value), generic)),
      x.value);

  // y= d*math.pow(2,-i)*x1 + y1
  generic = builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(x1.value), x1.value), builder.CreateLoad(getElementTypeFromValuePointer(i), i));
  builder.CreateStore(
      builder.CreateSelect(
          builder.CreateICmpEQ(builder.CreateLoad(getElementTypeFromValuePointer(d.value), d.value), zero),
          builder.CreateSub(builder.CreateLoad(getElementTypeFromValuePointer(y1.value), y1.value), generic),
          builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(y1.value), y1.value), generic)),
      y.value);

  builder.CreateStore(builder.CreateAdd(builder.CreateLoad(getElementTypeFromValuePointer(i), i), ConstantInt::get(Type::getInt32Ty(cont), 1)), i);

  builder.CreateBr(loop_entry);

  builder.SetInsertPoint(end_loop);

  if (fxpret.scalarFracBitsAmt() > arg_size - 3) {
    builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(theta.value), theta.value), fxpret.scalarFracBitsAmt() - arg_size + 3), theta.value);
  } else if (fxpret.scalarFracBitsAmt() < arg_size - 3) {
    builder.CreateStore(builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(theta.value), theta.value), -fxpret.scalarFracBitsAmt() + arg_size - 3), theta.value);
  }
  builder.CreateRet(builder.CreateLoad(getElementTypeFromValuePointer(theta.value), theta.value));

  return true;
}

bool createATan(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf)
{
  //
  newfs->deleteBody();
  Value *generic;
  Module *M = oldf->getParent();

  // retrieve context used in later instruction
  llvm::LLVMContext &cont(oldf->getContext());
  DataLayout dataLayout(M);
  LLVM_DEBUG(dbgs() << "\nGet Context " << &cont << "\n");
  // get first basick block of function
  BasicBlock::Create(cont, "Entry", newfs);
  BasicBlock *where = &(newfs->getEntryBlock());
  LLVM_DEBUG(dbgs() << "\nGet entry point " << where);
  IRBuilder<> builder(where, where->getFirstInsertionPt());
  // get return type fixed point
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

  LLVM_DEBUG(dbgs() << "fxpret: " << fxpret.scalarBitsAmt() << " frac part: " << fxpret.scalarFracBitsAmt() << " difference: " << fxpret.scalarBitsAmt() - fxpret.scalarFracBitsAmt() << "\n");

  /*
    Define LLVM integer types that will hold our variables.
    The internal variables will have a similar magnitude to the argument, so we can use the same data type with an additional bit for the integer part.
  */
  auto int_type = fxpret.scalarToLLVMType(cont);
  auto internal_fxpt = flttofix::FixedPointType(true, fxparg.scalarFracBitsAmt() - 5, fxparg.scalarBitsAmt());
  LLVM_DEBUG(dbgs() << "Internal fixed point type: ");
  int_type->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // Generate strings for constants names
  std::string S_ret_point = "." + std::to_string(fxpret.scalarFracBitsAmt());
  std::string S_int_point = "." + std::to_string(internal_fxpt.scalarFracBitsAmt());

  // ----------------------------------------------------

  // Pointer to the argument
  Value *arg_ptr = builder.CreateAlloca(int_type, nullptr, "arg");
  builder.CreateStore(newfs->getArg(0), arg_ptr);

  LLVM_DEBUG(dbgs() << "arg_ptr: ");
  arg_ptr->print(dbgs(), true);
  LLVM_DEBUG(dbgs() << "\n");

  // handle unsigned arg
  if (!fxparg.scalarIsSigned()) {
    builder.CreateStore(builder.CreateLShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr), ConstantInt::get(int_type, 1)), arg_ptr);
    fxparg.scalarFracBitsAmt() = fxparg.scalarFracBitsAmt() - 1;
    fxparg.scalarIsSigned() = true;
  }

  // TaffoMath::pair_ftp_value<llvm::Value *> arg(fxparg);
  // arg.value = newfs->arg_begin();
  auto truefxpret = fxpret;
  /*
  if ((fxpret.scalarBitsAmt() - fxpret.scalarFracBitsAmt()) < 5) {
    fxpret = flttofix::FixedPointType(true,
                                      fxpret.scalarBitsAmt() - 5,
                                      fxpret.scalarBitsAmt());
    LLVM_DEBUG(dbgs() << "New fxpret: " << fxpret << "\n");
  }

  */

  // ----------------------------------------------------
  // Basic blocks

  // Block for the initialization of the loop
  BasicBlock *init = BasicBlock::Create(cont, "init", newfs);

  // Blocks where we check loop boundaries
  BasicBlock *check_loop = BasicBlock::Create(cont, "check_loop", newfs);

  // Main loop bodies
  BasicBlock *loop_body = BasicBlock::Create(cont, "loop_body", newfs);

  // In case we did not need to return a special value, we will cast the result to the return type here
  BasicBlock *finalize = BasicBlock::Create(cont, "finalize", newfs);

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
  Value *i_iterator = builder.CreateAlloca(int_type, nullptr, "iterator");

  // Pointer to zero in the return fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_ret(fxpret);
  // Pointer to zero in the internal fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> zero_internal(internal_fxpt);
  // Pointer to one in the internal fixed point type
  TaffoMath::pair_ftp_value<llvm::Constant *> one(internal_fxpt);
  // The arctanh array table
  TaffoMath::pair_ftp_value<llvm::Constant *,
                            TaffoMath::TABLELENGHT>
      arctan_2power;

  // ----------------------------------------------------

  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, fxpret, zero_ret.value, zero_ret.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::one, internal_fxpt, one.value, one.fpt);
  TaffoMath::createFixedPointFromConst(
      cont, ref, TaffoMath::zero, internal_fxpt, zero_internal.value, zero_internal.fpt);

  zero_ret.value = TaffoMath::createGlobalConst(
      M, "zero" + S_ret_point, zero_ret.fpt.scalarToLLVMType(cont), zero_ret.value,
      dataLayout.getPrefTypeAlignment(zero_ret.fpt.scalarToLLVMType(cont)));
  zero_internal.value = TaffoMath::createGlobalConst(
      M, "zero_internal" + S_int_point, zero_internal.fpt.scalarToLLVMType(cont),
      zero_internal.value,
      dataLayout.getPrefTypeAlignment(zero_internal.fpt.scalarToLLVMType(cont)));
  one.value = TaffoMath::createGlobalConst(
      M, "one" + S_int_point, one.fpt.scalarToLLVMType(cont), one.value,
      dataLayout.getPrefTypeAlignment(one.fpt.scalarToLLVMType(cont)));

  // ----------------------------------------------------
  // Create the table for arctanh

  LLVM_DEBUG(dbgs() << "\n===== Create arctanh table ====="
                    << "\n");

  llvm::AllocaInst *pointer_to_arctan_array = nullptr;

  for (int i = 0; i < TaffoMath::TABLELENGHT; i++) {
    LLVM_DEBUG(dbgs() << "Element " << i << ":\n");
    arctan_2power.fpt.push_back(flttofix::FixedPointType(fxpret));
    Constant *tmp = nullptr;
    auto &current_fpt = arctan_2power.fpt.front();
    TaffoMath::createFixedPointFromConst(
        cont, ref, TaffoMath::arctan_2power[i], fxpret, tmp, current_fpt);
    arctan_2power.value.push_back(tmp);
    LLVM_DEBUG(dbgs() << "\n");
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
      TaffoMath::createGlobalConst(M, "arctan_g." + std::to_string(fxpret.scalarFracBitsAmt()), arctanArrayType,
                                   arctanConstArray, alignement_arctan);

  pointer_to_arctan_array = builder.CreateAlloca(arctanArrayType);
  pointer_to_arctan_array->setAlignment(llvm::Align(alignement_arctan));

  builder.CreateMemCpy(
      pointer_to_arctan_array, llvm::Align(alignement_arctan), arctan_g, llvm::Align(alignement_arctan),
      TaffoMath::TABLELENGHT * (int_type->getScalarSizeInBits() >> 3));
  LLVM_DEBUG(dbgs() << "\nAdd to newf arctan table"
                    << "\n");

  // calculate arctan

  LLVM_DEBUG(dbgs() << "Starting arctan routine"
                    << "\n");

  auto zero_internal_value = builder.CreateLoad(getElementTypeFromValuePointer(zero_internal.value), zero_internal.value, "zero_internal");
  LLVM_DEBUG(dbgs() << "zero: ");
  zero_internal_value->print(dbgs(), true);
  auto zero_ret_value = builder.CreateLoad(getElementTypeFromValuePointer(zero_ret.value), zero_ret.value, "zero_ret");
  LLVM_DEBUG(dbgs() << "\n");

  LLVM_DEBUG(dbgs() << "Zero value set"
                    << "\n");

  auto one_value = builder.CreateLoad(getElementTypeFromValuePointer(one.value), one.value, "one");
  //Shift right arg_value by 5
  auto arg_value = builder.CreateAShr(builder.CreateLoad(getElementTypeFromValuePointer(arg_ptr), arg_ptr, "arg_value"), ConstantInt::get(int_type, 5), "arg_value_shr_5");

  // Initialise x y z
  // x=1
  builder.CreateStore(one_value, x_ptr.value);
  // y=arg
  builder.CreateStore(arg_value, y_ptr.value);
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

  // i=0
  builder.CreateStore(builder.CreateLoad(getElementTypeFromValuePointer(zero_ret.value), zero_ret.value), i_iterator);

  builder.CreateBr(check_loop);
  builder.SetInsertPoint(check_loop);

  auto i_value = builder.CreateLoad(getElementTypeFromValuePointer(i_iterator), i_iterator, "i_value");
  // i < TABLELENGHT
  generic = builder.CreateICmpSLT(
      i_value,
      ConstantInt::get(int_type, TaffoMath::TABLELENGHT));
  // i < size of int
  Value *generic2 = builder.CreateICmpSLT(
      i_value,
      ConstantInt::get(int_type, int_type->getScalarSizeInBits()));
  builder.CreateCondBr(builder.CreateAnd(generic, generic2), loop_body,
                       finalize);

  builder.SetInsertPoint(loop_body);
  LLVM_DEBUG(dbgs() << "Start loop"
                    << "\n");

  // Current x y z values
  auto x_value = builder.CreateLoad(getElementTypeFromValuePointer(x_ptr.value), x_ptr.value, "x_curr");
  auto y_value = builder.CreateLoad(getElementTypeFromValuePointer(y_ptr.value), y_ptr.value, "y_curr");
  auto z_value = builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value, "z_curr");

  // sign = y >= 0 ? -1 : 1;
  Value *update_sign = builder.CreateSelect(
      builder.CreateICmpSGE(y_value, zero_internal_value, "arg_is_negative"),
      ConstantInt::get(int_type, -1), ConstantInt::get(int_type, 1), "update_sign");

  // update_sign > 0 ?
  auto update_sign_greater_zero = builder.CreateICmpSGT(update_sign, zero_internal_value, "update_sign_greater_zero");

  {
    // Update y. The update reads x.

    // Calculate x * (2 ^ -i)
    y_update = builder.CreateAShr(
        x_value, i_value, "y_upd_1");

    LLVM_DEBUG(dbgs() << "y_update 1 calculated"
                      << "\n");

    // Calculate (update_sign > 0 ? (x * (2 ^ -shift_amt)) : -(x * (2 ^ -shift_amt)));
    y_update = builder.CreateSelect(
        update_sign_greater_zero, y_update, builder.CreateSub(zero_internal_value, y_update, "minus_y_upd_1"), "y_upd_2");

    LLVM_DEBUG(dbgs() << "y_update 2 calculated"
                      << "\n");

    // y_{k+1} = y_k + y_update. Set to temp value since we will need to use y next.
    y_update = builder.CreateAdd(
        y_value, y_update, "y_upd_3");

    LLVM_DEBUG(dbgs() << "y_update 3 calculated"
                      << "\n");
  }

  {
    // Update x. The update reads y.

    // Calculate y * (2 ^ -shift_amt)
    x_update = builder.CreateAShr(
        y_value, i_value, "x_upd_1_loop2");

    LLVM_DEBUG(dbgs() << "x_update 1 calculated"
                      << "\n");

    // Calculate (update_sign > 0 ? -(y * (2 ^ -shift_amt)) : (y * (2 ^ -shift_amt)));
    x_update = builder.CreateSelect(
        update_sign_greater_zero, builder.CreateSub(zero_internal_value, x_update, "minus_x_upd_1"), x_update, "x_upd_2");

    LLVM_DEBUG(dbgs() << "x_update 2 calculated"
                      << "\n");

    // x_{k+1} = x_k + x_update
    x_update =
        builder.CreateAdd(x_value, x_update, "x_upd_3");

    LLVM_DEBUG(dbgs() << "x_update 3 calculated"
                      << "\n");
  }

  // Store y_update into y
  builder.CreateStore(y_update, y_ptr.value);

  // Store x_update into x
  builder.CreateStore(x_update, x_ptr.value);

  LLVM_DEBUG(dbgs() << "x and y updated"
                    << "\n");

  {
    // Update z

    // Calculate arctan_2power[i]
    z_update = builder.CreateGEP(getElementTypeFromValuePointer(pointer_to_arctan_array), pointer_to_arctan_array,
                                 {zero_ret_value, i_value}, "atan_2pwr_i_ptr");

    LLVM_DEBUG(dbgs() << "z_update: ");
    z_update->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    LLVM_DEBUG(dbgs() << "z_update 1 calculated"
                      << "\n");

    z_update = builder.CreateLoad(getElementTypeFromValuePointer(z_update), z_update, "atanh_2pwr_i");

    LLVM_DEBUG(dbgs() << "z_update 2 calculated"
                      << "\n");

    // z = z + (update_sign > 0 ? -arctanh_2power[i] : arctanh_2power[i]);
    z_update = builder.CreateSelect(
        update_sign_greater_zero, builder.CreateSub(zero_ret_value, z_update), z_update, "arg_update");

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
                                        ConstantInt::get(int_type, 1), "iterator_value_next"),
                      i_iterator);
  builder.CreateBr(check_loop);

  // Set the insert point to the end of the function, which is after the else.
  builder.SetInsertPoint(finalize);
  {
    LLVM_DEBUG(dbgs() << "End of arctan routine"
                      << "\n");

    if (fxpret.scalarFracBitsAmt() < truefxpret.scalarFracBitsAmt()) {
      builder.CreateStore(builder.CreateShl(builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value), truefxpret.scalarFracBitsAmt() - fxpret.scalarFracBitsAmt()), z_ptr.value);
    }

    auto return_value = builder.CreateLoad(getElementTypeFromValuePointer(z_ptr.value), z_ptr.value, "z_value_final");
    LLVM_DEBUG(dbgs() << "return_value: ");
    return_value->print(dbgs(), true);
    LLVM_DEBUG(dbgs() << "\n");

    builder.CreateBr(end);
    builder.SetInsertPoint(end);
    builder.CreateRet(return_value);
    return true;
  }
}
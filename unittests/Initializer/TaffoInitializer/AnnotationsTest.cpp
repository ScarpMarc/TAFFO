#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/raw_ostream.h"
#include "gtest/gtest.h"

#include "TaffoInitializer/TaffoInitializerPass.h"
#include "TestUtils.h"


namespace
{
using namespace taffo;
using namespace llvm;


class AnnotationsTest : public testing::Test
{
protected:
  const std::string STARTP_NOT_INIT_ERR = "__taffo_vra_starting_function not initialized to anything or initialized incorrectly!";
  const std::string STARTP_BAD_INIT_ERR = "__taffo_vra_starting_function initialized incorrectly!";

  std::string code;
  taffo::ValueInfo info;
  llvm::Value *val{};
  llvm::LLVMContext Context;


  TaffoInitializer initializer;

  AnnotationsTest()
  {
    llvm::install_fatal_error_handler(FatalErrorHandler, nullptr);
  }

  ~AnnotationsTest() override
  {
    llvm::remove_fatal_error_handler();
  }

  /**
   * @brief Check the correctness of parsed metadata against a fixed template
   *
   * Annotation string: "target('test') scalar(range(0, 10) type(1 2) error(3.1415) disabled final)"
   *
   * @param toCheck the metadata to check
   * @return @c true if the metadata correspond to the intended values,@c false otherwise
   */
  static void checkMD(const ValueInfo &toCheck)
  {
    std::shared_ptr<mdutils::MDInfo> mdinfo = toCheck.metadata;
    auto *metadata = cast<mdutils::InputInfo>(mdinfo.get());

    // range
    auto min = metadata->IRange->Min;
    auto max = metadata->IRange->Max;
    EXPECT_EQ(min, 0);
    EXPECT_EQ(max, 10);

    // type
    auto width = cast<mdutils::FPType>(metadata->IType.get())->getWidth();
    auto pointPos = cast<mdutils::FPType>(metadata->IType.get())->getPointPos();
    auto isSigned = cast<mdutils::FPType>(metadata->IType.get())->isSigned();
    EXPECT_EQ(width, 1);
    EXPECT_EQ(pointPos, 2);
    EXPECT_TRUE(isSigned);

    auto error = *metadata->IError;
    EXPECT_EQ(error, 3.1415);

    EXPECT_EQ(toCheck.backtrackingDepthLeft, 0);
  }
};


TEST_F(AnnotationsTest, StartingPoint_None)
{
  code = R"(
    define dso_local i32 @main() #0 {
        ret i32 0
    }
    )";

  std::unique_ptr<llvm::Module> M = makeLLVMModule(Context, code);
  llvm::Function *F = initializer.findStartingPointFunctionGlobal(*M);
  ASSERT_EQ(F, nullptr);
}

TEST_F(AnnotationsTest, StartingPoint_Set)
{
  code = R"(
    @__taffo_vra_starting_function = dso_local global i8* bitcast (i32 ()* @main to i8*), align 8

    define dso_local i32 @main() #0 {
        ret i32 0
    }
    )";

  std::unique_ptr<llvm::Module> M = makeLLVMModule(Context, code);
  llvm::Function *F = initializer.findStartingPointFunctionGlobal(*M);
  ASSERT_NE(F, nullptr);
  EXPECT_EQ(F->getName(), "main");

  F = initializer.findStartingPointFunctionGlobal(*M);
  EXPECT_EQ(F, nullptr);
}

TEST_F(AnnotationsTest, StartingPoint_Unset)
{
  code = R"(
    @__taffo_vra_starting_function = dso_local global i8* null, align 8

    define dso_local i32 @main() #0 {
        ret i32 0
    }
    )";
  std::unique_ptr<llvm::Module> M = makeLLVMModule(Context, code);
  try {
    llvm::Function *F = initializer.findStartingPointFunctionGlobal(*M);
  } catch (const std::exception &e) {
    EXPECT_STREQ(e.what(), STARTP_NOT_INIT_ERR.c_str());
  }
}

TEST_F(AnnotationsTest, StartingPoint_NotAFunction)
{
  code = R"(
    @__taffo_vra_starting_function = dso_local constant i32 0, align 4

    define dso_local i32 @main() #0 {
      ret i32 0
    }
    )";
  std::unique_ptr<llvm::Module> M = makeLLVMModule(Context, code);
  try {
    llvm::Function *F = initializer.findStartingPointFunctionGlobal(*M);
  } catch (const std::exception &e) {
    EXPECT_STREQ(e.what(), STARTP_NOT_INIT_ERR.c_str());
  }
}


TEST_F(AnnotationsTest, ParseAnnotation_GlobalVariable)
{
  code = R"(
    @var = dso_local global float 0.000000e+00, align 4
    @.str = private unnamed_addr constant [75 x i8] c"target('test') scalar(range(0, 10) type(1 2) error(3.1415) disabled final)\00", section "llvm.metadata"
    @.str.1 = private unnamed_addr constant [10 x i8] c"testing.c\00", section "llvm.metadata"
    @llvm.global.annotations = appending global
    [1 x { i8*, i8*, i8*, i32, i8* }]
    [{ i8*, i8*, i8*, i32, i8* } {
      i8* bitcast (float* @var to i8*),
      i8* getelementptr inbounds ([75 x i8], [75 x i8]* @.str, i32 0, i32 0),
      i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.1, i32 0, i32 0),
      i32 1,
      i8* null
    }], section "llvm.metadata"

    define dso_local i32 @main() #0 {
      ret i32 0
  })";
  std::unique_ptr<llvm::Module> M = makeLLVMModule(Context, code);
  GlobalVariable *globalVars = M->getGlobalVariable("llvm.global.annotations");
  ASSERT_NE(globalVars, nullptr);

  MultiValueMap<llvm::Value *, ValueInfo> variables;
  auto *anno = cast<ConstantStruct>(globalVars->getInitializer()->getOperand(0));
  auto *annoPtrInstr = cast<ConstantExpr>(anno->getOperand(1));
  auto *instr = cast<ConstantExpr>(anno->getOperand(0))->getOperand(0);
  bool startingPoint;
  bool res = initializer.parseAnnotation(variables, annoPtrInstr, instr, &startingPoint);

  ASSERT_TRUE(res);

  Value *first = variables.begin()->first;
  ASSERT_EQ(first, instr);
  checkMD(variables.begin()->second);
  EXPECT_TRUE(startingPoint);
}

TEST_F(AnnotationsTest, ParseAnnotation_Function)
{
  code = R"(
    @.str = private unnamed_addr constant [75 x i8] c"target('test') scalar(range(0, 10) type(1 2) error(3.1415) disabled final)\00", section "llvm.metadata"
    @.str.1 = private unnamed_addr constant [10 x i8] c"testing.c\00", section "llvm.metadata"
    @llvm.global.annotations = appending global
    [1 x { i8*, i8*, i8*, i32, i8* }]
    [{ i8*, i8*, i8*, i32, i8* } {
      i8* bitcast (float ()* @fun to i8*),
      i8* getelementptr inbounds ([75 x i8], [75 x i8]* @.str, i32 0, i32 0),
      i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.1, i32 0, i32 0),
      i32 10,
      i8* null
    }], section "llvm.metadata"

    define dso_local i32 @main() #0 {
      %1 = alloca float, align 4
      %2 = call float @fun()
      store float %2, float* %1, align 4
      ret i32 0
    }

    define dso_local float @fun() #0 {
      ret float 0x400921CAC0000000
    }
  )";

  std::unique_ptr<llvm::Module> M = makeLLVMModule(Context, code);
  GlobalVariable *globalVars = M->getGlobalVariable("llvm.global.annotations");
  ASSERT_NE(globalVars, nullptr);

  MultiValueMap<llvm::Value *, ValueInfo> variables;
  auto *anno = cast<ConstantStruct>(globalVars->getInitializer()->getOperand(0));
  auto *annoPtrInstr = cast<ConstantExpr>(anno->getOperand(1));
  auto *instr = cast<ConstantExpr>(anno->getOperand(0))->getOperand(0);
  bool startingPoint;
  bool res = initializer.parseAnnotation(variables, annoPtrInstr, instr, &startingPoint);

  ASSERT_TRUE(res);

  Value *first = variables.begin()->first;
  auto instructions = M->getFunction("main")->getBasicBlockList().begin()->getInstList().begin();
  auto *user = cast<llvm::Value>(instructions.operator++());
  ASSERT_EQ(first, user);
  checkMD(variables.begin()->second);
  EXPECT_TRUE(startingPoint);

  auto fun = M->getFunction("fun");
  EXPECT_TRUE(initializer.enabledFunctions.contains(fun));
  EXPECT_EQ(initializer.enabledFunctions.size(), 1);
}

TEST_F(AnnotationsTest, ParseAnnotation_LocalVariable)
{
  code = R"(
    @.str = private unnamed_addr constant [75 x i8] c"target('test') scalar(range(0, 10) type(1 2) error(3.1415) disabled final)\00", section "llvm.metadata"
    @.str.1 = private unnamed_addr constant [10 x i8] c"testing.c\00", section "llvm.metadata"

    define dso_local i32 @main() #0 {
      %1 = alloca float, align 4
      %2 = bitcast float* %1 to i8*
      call void @llvm.var.annotation(
        i8* %2,
        i8* getelementptr inbounds ([75 x i8], [75 x i8]* @.str, i32 0, i32 0),
        i8* getelementptr inbounds ([10 x i8], [10 x i8]* @.str.1, i32 0, i32 0),
        i32 3,
        i8* null
      )
      ret i32 0
    }

  declare void @llvm.var.annotation(i8*, i8*, i8*, i32, i8*) #1
  )";
  std::unique_ptr<llvm::Module> M = makeLLVMModule(Context, code);
  auto instruction = M->getFunction("main")->getBasicBlockList().begin()->getInstList().begin();
  auto *user = cast<llvm::Value>(instruction); // the register %1
  instruction = instruction.operator++().operator++();

  // check that we're picking the right instruction
  auto *callInstr = cast<llvm::CallInst>(instruction);
  ASSERT_NE(callInstr, nullptr);
  ASSERT_NE(callInstr->getCalledFunction(), nullptr);

  MultiValueMap<llvm::Value *, ValueInfo> variables;
  auto *annoPtrInstr = cast<llvm::ConstantExpr>(instruction->getOperand(1));
  auto *instr = instruction->getOperand(0);
  bool startingPoint;
  bool res = initializer.parseAnnotation(variables, annoPtrInstr, instr, &startingPoint);

  ASSERT_TRUE(res);

  Value *first = variables.begin()->first;
  ASSERT_EQ(first, user);
  checkMD(variables.begin()->second);
  EXPECT_TRUE(startingPoint);
}
} // namespace

#pragma once
#include "FixedPointType.h"
#include "LLVMFloatToFixedPass.h"
#include "TAFFOMath.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"

namespace flttofix
{

bool createSqrt(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf);
bool createHypot(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf);
bool createPow(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf);
bool createCbrt(FloatToFixed *ref, llvm::Function *newfs, llvm::Function *oldf);


/// Number of iterations for the sqrt CORDIC algorithm
constexpr int cordic_sqrt_iterations = TaffoMath::TABLELENGHT;
/// Width of the extended, internal representation for the sqrt CORDIC algorithm
const int cordic_sqrt_internal_width = 32;
/// Fractional part of the internal representation for the sqrt CORDIC algorithm. We estimate we need 22 bits for the integer part + 1 for the sign.
const int cordic_sqrt_internal_width_fractional = 0; //cordic_sqrt_internal_width - 23;

const double sqrt2m1 = 0.41421356237309504880168872421;
    
constexpr double compute_An(const int &n)
{
    double An = 1.0;
    for (int i = 1; i < n; i++)
    {
        An *= std::sqrt(1 - std::pow(2, -2 * i));
        if (i == 4 || i == 13 || i==40)
        {
            An *= std::sqrt(1 - std::pow(2, -2 * i));
        }
    }
    return An;
}

} // namespace flttofix
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

/// Number of iterations for the sqrt CORDIC algorithm
constexpr int cordic_sqrt_iterations = TaffoMath::TABLELENGHT;
/// Width of the extended, internal representation for the sqrt CORDIC algorithm
const int cordic_sqrt_internal_width = 64;
/// Fractional part of the internal representation for the sqrt CORDIC algorithm. We estimate we need 22 bits for the integer part + 1 for the sign.
const int cordic_sqrt_internal_width_fractional = 64 - 23;
    
constexpr double compute_An_inv(const int &n)
{
    double An = 1.0;
    for (int i = 1; i < n; i++)
    {
        An *= std::sqrt(1 + std::pow(2, -2 * i));
        if (i == 4 || i == 13 || i==40)
        {
            An *= std::sqrt(1 + std::pow(2, -2 * i));
        }
    }
    return 1.0 / An;
}

} // namespace flttofix
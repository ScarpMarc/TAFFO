/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* jacobi-1d.c: this file is part of PolyBench/C */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include benchmark-specific header. */
#include "jacobi-1d.h"

#ifdef _LAMP
DATA_TYPE POLYBENCH_1D(A_float,N,n);
#endif

/* Array initialization. */
static
void init_array (int n,
		 DATA_TYPE POLYBENCH_1D(A,N,n),
		 DATA_TYPE POLYBENCH_1D(B,N,n))
{
  int i __attribute__((annotate("scalar(range(-" PB_XSTR(N) ", " PB_XSTR(N) ") final)")));

  for (i = 0; i < n; i++)
      {
	A[i] = ((DATA_TYPE) i+ 2) / n;
	B[i] = ((DATA_TYPE) i+ 3) / n;
      }
}


/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
#if (!defined _LAMP) || (defined _PRINT_OUTPUT)
static
void print_array(int n,
		 DATA_TYPE POLYBENCH_1D(A,N,n))

{
  int i;

  POLYBENCH_DUMP_START;
  POLYBENCH_DUMP_BEGIN("A");
  for (i = 0; i < n; i++)
    {
      if (i % 20 == 0) fprintf(POLYBENCH_DUMP_TARGET, "\n");
      fprintf(POLYBENCH_DUMP_TARGET, DATA_PRINTF_MODIFIER, A[i]);
    }
  POLYBENCH_DUMP_END("A");
  POLYBENCH_DUMP_FINISH;
}
#endif


/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static
void kernel_jacobi_1d(int tsteps,
			    int n,
			    DATA_TYPE POLYBENCH_1D(A,N,n),
			    DATA_TYPE POLYBENCH_1D(B,N,n))
{
  int t, i;

#pragma scop
  for (t = 0; t < _PB_TSTEPS; t++)
    {
      for (i = 1; i < _PB_N - 1; i++)
	B[i] = 0.33333 * (A[i-1] + A[i] + A[i + 1]);
      for (i = 1; i < _PB_N - 1; i++)
	A[i] = 0.33333 * (B[i-1] + B[i] + B[i + 1]);
    }
#pragma endscop

}


int main(int argc, char** argv)
{
  /* Retrieve problem size. */
  int n = N;
  int tsteps = TSTEPS;

  /* Variable declaration/allocation. */
  POLYBENCH_1D_ARRAY_DECL(A, DATA_TYPE __attribute__((annotate("target('A') scalar(range(" PB_XSTR(VAR_A_MIN) "," PB_XSTR(VAR_A_MAX) ") final)"))), N, n);
  POLYBENCH_1D_ARRAY_DECL(B, DATA_TYPE __attribute__((annotate("scalar(range(" PB_XSTR(VAR_B_MIN) "," PB_XSTR(VAR_B_MAX) ") final)"))), N, n);


  /* Initialize array(s). */
  init_array(n, POLYBENCH_ARRAY(A), POLYBENCH_ARRAY(B));

  #if SCALING_FACTOR!=1
    scale_1d(N, POLYBENCH_ARRAY(A), SCALING_FACTOR);
    scale_1d(N, POLYBENCH_ARRAY(B), SCALING_FACTOR);
  #endif

  #ifdef COLLECT_STATS
    stats_header();
    stats_scalar("tsteps", tsteps);
    stats_1d("A", N, POLYBENCH_ARRAY(A));
    stats_1d("B", N, POLYBENCH_ARRAY(B));
  #endif

  #ifndef _LAMP
    /* Start timer. */
    polybench_start_instruments;
  #endif

  timer_start();
  /* Run kernel. */
  kernel_jacobi_1d(tsteps, n, POLYBENCH_ARRAY(A), POLYBENCH_ARRAY(B));
  timer_stop();

#ifdef COLLECT_STATS
  stats_scalar("tsteps", tsteps);
  stats_1d("A", N, POLYBENCH_ARRAY(A));
  stats_1d("B", N, POLYBENCH_ARRAY(B));
#endif

#ifndef _LAMP
  /* Stop and print timer. */
  polybench_stop_instruments;
  polybench_print_instruments;

  /* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  polybench_prevent_dce(print_array(n, POLYBENCH_ARRAY(A)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(A);
  POLYBENCH_FREE_ARRAY(B);
#else
  for (int i = 0; i < n; i++)
    A_float[i] = A[i];
#ifdef _PRINT_OUTPUT
  polybench_prevent_dce(print_array(n, POLYBENCH_ARRAY(A_float)));
#endif
#endif

  return 0;
}

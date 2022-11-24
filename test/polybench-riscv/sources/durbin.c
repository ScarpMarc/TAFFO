/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* durbin.c: this file is part of PolyBench/C */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include <polybench.h>

/* Include benchmark-specific header. */
#include "durbin.h"

#ifdef _LAMP
float POLYBENCH_1D(y_float, N, n);
#endif

/* Array initialization. */
static
void init_array (int n,
		 DATA_TYPE POLYBENCH_1D(r,N,n),
                  DATA_TYPE POLYBENCH_1D(y,N,n))
{
  int i __attribute__((annotate("scalar(range(0.0, " PB_XSTR(N) ") final)")));

  for (i = 0; i < n; i++)
    {
      r[i] = (n+1-i);
      y[i] = 0;
    }
}


#if (!defined _LAMP) || (defined _PRINT_OUTPUT)
/* DCE code. Must scan the entire live-out data.
   Can be used also to check the correctness of the output. */
static
void print_array(int n,
		 DATA_TYPE POLYBENCH_1D(y,N,n))

{
  int i;

  POLYBENCH_DUMP_START;
  POLYBENCH_DUMP_BEGIN("y");
  for (i = 0; i < n; i++) {
    if (i % 20 == 0) fprintf (POLYBENCH_DUMP_TARGET, "\n");
    fprintf (POLYBENCH_DUMP_TARGET, DATA_PRINTF_MODIFIER, y[i]);
  }
  POLYBENCH_DUMP_END("y");
  POLYBENCH_DUMP_FINISH;
}
#endif


/* Main computational kernel. The whole function will be timed,
   including the call and return. */
static
void kernel_durbin(int n,
		   DATA_TYPE POLYBENCH_1D(r,N,n),
		   DATA_TYPE POLYBENCH_1D(y,N,n))
{
 DATA_TYPE __attribute__((annotate("scalar()"))) z[N];
 DATA_TYPE __attribute__((annotate("scalar(range(-2, 2) final)"))) alpha;
 DATA_TYPE __attribute__((annotate("scalar(range(-2, 2) final)"))) beta;
 DATA_TYPE __attribute__((annotate("scalar()"))) sum;

 int i = 0, k = 1;

#pragma scop
 y[k-i-1] = -r[k-i-1];
 beta = SCALAR_VAL(1.0);
 alpha = -r[k-i-1];

 DATA_TYPE constOneVal = 1.0f;

 for (k = 1; k < _PB_N; k++) {
   beta = (constOneVal-alpha*alpha)*beta;
   sum = SCALAR_VAL(0.0);
   for (i=0; i<k; i++) {
      sum += r[k-i-1]*y[i];
   }
   alpha = - (r[k] + sum)/beta;

   for (i=0; i<k; i++) {
      z[i] = y[i] + alpha*y[k-i-1];
   }
   for (i=0; i<k; i++) {
     y[i] = z[i];
   }
   y[k] = alpha;
 }
#pragma endscop

}


int main(int argc, char** argv)
{
  /* Retrieve problem size. */
  int n = N;

  /* Variable declaration/allocation. */
  POLYBENCH_1D_ARRAY_DECL(r, DATA_TYPE __attribute__((annotate("scalar(range(" PB_XSTR(VAR_r_MIN) "," PB_XSTR(VAR_r_MAX) ") final)"))), N, n);
  POLYBENCH_1D_ARRAY_DECL(y, DATA_TYPE __attribute__((annotate("target('y') scalar(range(" PB_XSTR(VAR_y_MIN) "," PB_XSTR(VAR_y_MAX) ") final)"))), N, n);


  /* Initialize array(s). */
  init_array (n, POLYBENCH_ARRAY(r), POLYBENCH_ARRAY(y));

  scale_1d(N, POLYBENCH_ARRAY(r), SCALING_FACTOR);
  scale_1d(N, POLYBENCH_ARRAY(y), SCALING_FACTOR);

#ifdef COLLECT_STATS
  stats_header();
  stats_1d("r", N, POLYBENCH_ARRAY(r));
  stats_1d("y", N, POLYBENCH_ARRAY(y));
#endif

#ifndef _LAMP
  /* Start timer. */
  polybench_start_instruments;
#endif

  timer_start();
  /* Run kernel. */
  kernel_durbin (n,
		 POLYBENCH_ARRAY(r),
		 POLYBENCH_ARRAY(y));
  timer_stop();

#ifdef COLLECT_STATS
  stats_1d("r", N, POLYBENCH_ARRAY(r));
  stats_1d("y", N, POLYBENCH_ARRAY(y));
#endif

#ifndef _LAMP
  /* Stop and print timer. */
  polybench_stop_instruments;
  polybench_print_instruments;

  /* Prevent dead-code elimination. All live-out data must be printed
     by the function call in argument. */
  polybench_prevent_dce(print_array(n, POLYBENCH_ARRAY(y)));

  /* Be clean. */
  POLYBENCH_FREE_ARRAY(r);
  POLYBENCH_FREE_ARRAY(y);
#else
  for (int i = 0; i < n; i++)
    y_float[i] = y[i];
#ifdef _PRINT_OUTPUT
  polybench_prevent_dce(print_array(n, POLYBENCH_ARRAY(y_float)));
#endif
#endif

  return 0;
}

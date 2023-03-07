#include <fenv.h>
#include <stdint.h>
#include <stdio.h>
#define TRUE 1
#define FALSE 0
#include "data.h"
#ifndef M
#define M 10000
#endif

#ifdef APP_MFUNC
double sin(double x)
{
  return x - ((x * x * x) / 6.0f);
}

double cos(double x)
{
  return 1.0f - (x * x * 0.25f);
}

double atan(double x)
{
  return x - ((x * x * x) / 3.0f);
}
#else
#include <math.h>
#endif

float ex0(float x, float y)
{
  float pi = 3.14159265359f;
  float radiant = atan((y / x));
  return radiant * (180.0f / pi);
}

int internal_main()
{
  static const int len = sizeof(arr) / sizeof(arr[0]) / 2;
  float __attribute__((annotate("target('main') scalar(range(1, 100))")))
  x[len];
  float __attribute__((annotate("scalar(range(1, 100))"))) y[len];

  float res[len];
  for (int i = 0; i < len; ++i) {

    x[i] = arr[i * 2];
    y[i] = arr[i * 2 + 1];
  }

  for (int i = 0; i < M; ++i) {


    long long start = miosix::getTime();
    for (int j = 0; j < len; ++j) {
      res[j] = ex0(x[j], y[j]);
    }

    long long end = miosix::getTime();

    if (end > start) {
      printf("Cycles: %lli\n", end - start);
    }
  }
  printf("Values Begin\n");
  for (int j = 0; j < len; ++j) {
    printf("%f\n", res[j]);
  }
  printf("Values End\n");
  return 0;
}

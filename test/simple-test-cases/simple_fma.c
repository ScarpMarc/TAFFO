/// TAFFO_TEST_ARGS -fixm -Xvra -propagate-all -lm
#include <math.h>
#include <stdio.h>

int main(int argc, char *argv[])
{
  int n = 0;
  float tmp1 __attribute((annotate("target('a') scalar(range(-100, 100))"))) = -100.0f;
  float tmp2 __attribute((annotate("target('a') scalar(range(-1000, 1000))"))) = -1000.0f;
  float tmp3 __attribute((annotate("target('a') scalar(range(-10, 10))"))) = -10.0f;

  for (int i = 0; i < 2000; i++) {
    float p = fma(tmp1, tmp2, tmp3);
    printf("fma(%f, %f, %f): %f\n", tmp1, tmp2, tmp3, p);
    tmp1 += 0.1f;
    tmp2 += 1.0f;
    tmp3 += 0.01f;
  }

  return 0;
}
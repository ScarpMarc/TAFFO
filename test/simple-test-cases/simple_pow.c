/// TAFFO_TEST_ARGS -fixm -Xvra -propagate-all -lm
#include <math.h>
#include <stdio.h>

int main(int argc, char *argv[])
{
  int n = 0;
  float tmp __attribute((annotate("target('a') scalar(range(0.001, 200))"))) = 1.0f;
  float tmp2 __attribute((annotate("target('b') scalar(range(0.001, 200))"))) = 2.0f;

  for (int i = 0; i < 50; i++)
  {
    //printf("Iteration %d\n", i);
    float p = pow(tmp, tmp2);
    printf("pow(%f, %f) = %f\n", tmp, tmp2, p);
    tmp += 0.5f;
    tmp2 += 0.5f;
  }

  return 0;
}
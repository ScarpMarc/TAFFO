/// TAFFO_TEST_ARGS -fixm -Xvra -propagate-all -lm
#include <math.h>
#include <stdio.h>

int main(int argc, char *argv[])
{
  int n = 0;
  float tmp __attribute((annotate("target('a') scalar(range(0.001, 200))"))) = 0.1f;
  float tmp2 __attribute((annotate("target('b') scalar(range(0.001, 200))"))) = 0.2f;

  for (int i = 0; i < 20; i++)
  {
    //printf("Iteration %d\n", i);
    float p = pow(tmp, tmp2);
    printf("pow(%f, %f) = %f\n", tmp, tmp2, p);
    tmp += 0.1f;
    tmp2 += 0.1f;
  }

  return 0;
}
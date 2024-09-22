/// TAFFO_TEST_ARGS -fixm -Xvra -propagate-all -lm
#include <math.h>
#include <stdio.h>

int main(int argc, char *argv[])
{
  int n = 0;
  float tmp __attribute((annotate("target('a') scalar(range(-5.00023283064365386963, 200))"))) = -5.00023283064365386963f;

  for (int i = 0; i < 50; i++)
  {
    //printf("Iteration %d\n", i);
    float p = log2(tmp);
    printf("log2(%f) = %f\n", tmp, p);
    tmp += 5.0f;
  }
  return 0;
}
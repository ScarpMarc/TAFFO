/// TAFFO_TEST_ARGS -fixm -Xvra -propagate-all -lm
#include <math.h>
#include <stdio.h>

int main(int argc, char *argv[])
{
  int n = 0;
  float tmp __attribute((annotate("target('a') scalar(range(-10, 200))"))) = -10.1f;

  for (int i = 0; i < 50; i++)
  {
    //printf("Iteration %d\n", i);
    float p = log1p(tmp);
    printf("log1p(%f) = %f\n", tmp, p);
    tmp += 5.0f;
  }
  return 0;
}
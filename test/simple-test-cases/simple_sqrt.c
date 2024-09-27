/// TAFFO_TEST_ARGS -fixm -Xvra -propagate-all -lm
#include <math.h>
#include <stdio.h>

int main(int argc, char *argv[])
{
  int n = 0;
  float tmp __attribute((annotate("target('a') scalar(range(0.001, 200))"))) = 0.10f;

  for (int i = 0; i < 50; i++)
  {
    //printf("Iteration %d\n", i);
    float p = sqrt(tmp);
    printf("sqrt(%f) = %f\n", tmp, p);
    tmp += 0.5f;
  }

  return 0;
}
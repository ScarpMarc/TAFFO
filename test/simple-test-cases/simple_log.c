/// TAFFO_TEST_ARGS -fixm -Xvra -propagate-all -lm
#include <math.h>
#include <stdio.h>

int main(int argc, char *argv[])
{
  int n = 0;
  float tmp __attribute((annotate("target('a') scalar(range(-20, 250))"))) = -20.00001;

  for (int i = 0; i < 50; i++)
  {
    //printf("Iteration %d\n", i);
    float p = log(tmp);
    printf("log(%f) = %f\n", tmp, p);
    tmp += 5.0f;
  }
  return 0;
}
/// TAFFO_TEST_ARGS -fixm -Xvra -propagate-all -lm
#include <math.h>
#include <stdio.h>

int main(int argc, char *argv[])
{
  float mag __attribute((annotate("target('a') scalar(range(-100, 100))"))) = -100.0f;
  float sgn __attribute((annotate("target('a') scalar(range(-1, 1))"))) = -1.0f;

  // copysign(magnitude, sign)

  for (int i = 0; i < 2000; i++) {
    float p = copysignf(mag, sgn);
    printf("mag: %f, sgn: %f, res: %f\n", mag, sgn, p);
    mag += 0.1f;
    sgn = -sgn;
  }

  return 0;
}

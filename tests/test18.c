#include <stdlib.h>

// should fail verification iff bound is sufficiently high
void fn(int i) {
  if (i < 5) {
    return;
  }

  for (int j = 1; j <= i; ++j) {
    int *p = malloc(8);
    if (j < i) { free(p); }
  }
}

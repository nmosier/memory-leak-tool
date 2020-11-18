#include <stdlib.h>

// should fail verification if bound isn't tiny
void fn(int i) {
  if (i == 1) { return; }

  for (int j = 1; j <= i; ++j) {
    int *p = malloc(8);
    if (j < i) { free(p); }
  }
}

#include <stdlib.h>

void fn(void) {
  for (int i = 1; i < 100; ++i) {
    int *p = malloc(8);
    free(p);
  }
}

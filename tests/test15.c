#include <stdlib.h>

void fn(int i, int j) {
  void *p = malloc(8);
  if (i + j == 0 && i > 1) {
    free(p);
  }
}

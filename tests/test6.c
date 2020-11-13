#include <stdlib.h>

void fn(int i) {
   void *p = malloc(8);
   free(p + i);
}

#include <stdlib.h>

void fn(void) {
   int i;
   int *p = &i;
   free(p);
}

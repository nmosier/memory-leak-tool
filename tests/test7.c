#include <stdlib.h>

void fn(void *p) {
   if (p != NULL) {
      free(p);
   }
}

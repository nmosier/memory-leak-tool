#include <stdlib.h>

void fn(int i) {
   void *p = malloc(8);
   if (i >= 0) {
      free(p);
   }
}
  

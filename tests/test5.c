#include <stdlib.h>

void fn(int i) {
   int j = i ? i : 42;
   void *p = NULL;
   if (j != 42) {
      p = malloc(8);
   }
   
   free(p);
}

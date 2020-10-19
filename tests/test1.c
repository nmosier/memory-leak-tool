#include <stdlib.h>

int main(void) {
   void *p = malloc(8);
   free(p);
   return 0;
}

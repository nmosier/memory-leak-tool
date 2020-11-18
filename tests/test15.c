#include <stdlib.h>
#include <sys/mman.h>

void fn(void) {
   void *map;
   if ((map = mmap(NULL, 4096, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0))
       == MAP_FAILED) {
      return;
   }
   munmap(map, 4096);
}

#include <sys/mman.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>

int fn(const char *path, char buf[4096]) {
   int fd;
   void *map = MAP_FAILED;
   int rv = -1;

   if ((fd = open(path, O_RDONLY)) < 0) {
      goto cleanup;
   }

   if ((map = mmap(NULL, 4096, PROT_READ, MAP_PRIVATE, fd, 0)) == MAP_FAILED) {
      goto cleanup;
   }

   memcpy(buf, map, 4096);
   
   rv = 0;
   
 cleanup:
   if (map != MAP_FAILED) {
      munmap(map, 4096);
   }
   if (fd >= 0) {
      close(fd);
   }
   
   return rv;
}

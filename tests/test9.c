#include <unistd.h>
#include <fcntl.h>

void fn(const char *path) {
   int fd;

   if ((fd = open(path, O_RDONLY)) < 0) {
      return;
   }

   close(fd);
}

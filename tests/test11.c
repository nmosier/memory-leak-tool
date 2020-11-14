#include <unistd.h>
#include <fcntl.h>

void fn(const char *p1, const char *p2) {
   int fd1, fd2;

   if ((fd1 = open(p1, O_RDONLY)) < 0) {
      return;
   }

   if ((fd2 = open(p1, O_RDONLY)) < 0) {
      return;
   }

   close(fd1);
   close(fd2);
}

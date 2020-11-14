#include <fcntl.h>
#include <unistd.h>

void fn(const char *path) {
   int fd = open(path, O_RDONLY);
   close(fd);
}

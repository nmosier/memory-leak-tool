#ifndef __MYIO_H
#define __MYIO_H

typedef struct {
   int f_fd;       // file descriptor
   size_t f_size;  // size of file
   int f_flags;    // file permissions
   void *m_base;   // base of mmap'ed file
   void *m_rwp;    // read-write pointer
   size_t m_size;  // length of mapped memory (generally greater than f_size)
} MYFILE;

MYFILE *myopen(const char *pathname, int flags);
int myclose(MYFILE *file);
ssize_t myread(MYFILE *file, void *buf, size_t count);
ssize_t mywrite(MYFILE *file, const void *buf, size_t count);
off_t myseek(MYFILE *file, off_t offset, int whence);
int myflush(MYFILE *file);
int mytruncate(MYFILE *file, ssize_t f_newsize, ssize_t m_newsize);   

void *mremap(void *, size_t, size_t, int, ...);

#define MREMAP_MAYMOVE 1

#endif

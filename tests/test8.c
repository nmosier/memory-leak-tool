#define DEBUG 1
#define _GNU_SOURCE

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <errno.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <fcntl.h>
#include "myio.h"

/* memory mapping macros & prototypes */
#define PAGE_SIZE   (sysconf(_SC_PAGE_SIZE))
size_t page_round_plus1(size_t size);

/* arithmetic prototypes */
int oabs(off_t offset);
int chk_overflow_add(off_t val1, off_t val2);
int chk_overflow_sub(off_t val1, off_t val2);

/* MYFILE macros & prototypes */
#define MYFILE_ACCESS_MASK        (O_RDONLY | O_WRONLY | O_RDWR)
int myfile_readable(MYFILE *file);
int myfile_writeable(MYFILE *file);
off_t myfile_offset(MYFILE *file);
off_t myfile_f_rembytes(MYFILE *file);
off_t myfile_m_rembytes(MYFILE *file);





/* myopen()
 * DESC: opens new file at _pathname_ with given flags.
 * ARGS:
 *  - pathname: path to file
 *  - flags: mask of flags specifying mode. See manpage for open(2)
 * RETV: returns pointer to MYFILE struct upon success; returns
 *        NULL upon error.
 */
MYFILE *myopen(const char *pathname, int flags) {
   MYFILE *file;
   void *m_base;
   int fd;
   size_t f_size, m_size;
   struct stat f_info;
   int prot, oflags;

   /* modify flags to be suitable for mmap */
   oflags = (flags & O_WRONLY) ? ((flags & ~O_WRONLY) | O_RDWR) : flags;
   
   /* open file */
   if ((fd = open(pathname, oflags, 0664)) < 0) {
      return NULL; // open error
   }
   
   /* get file size */
   if (fstat(fd, &f_info) < 0) {
      return NULL;
   }
   f_size = f_info.st_size;
   
   /* convert _flags_ to _prot_ (protection) flags for mmap */
   switch ((flags & MYFILE_ACCESS_MASK)) {
   case O_WRONLY:
   case O_RDWR:
      prot = PROT_READ|PROT_WRITE;
      break;
   case O_RDONLY:
      prot = PROT_READ;
      break;
   default:
      /* invalid combination of read/write permissions */
      errno = EINVAL;
      return NULL;
   }

   /* compute memory map size */
   if ((flags & MYFILE_ACCESS_MASK) == O_RDONLY) {
      m_size = f_size; // won't ever resize file
   } else {
      /* resize file to have length of m_size */
      m_size = page_round_plus1(f_size);
      if (ftruncate(fd, m_size) < 0) {
         return NULL;
      }
   }

   /* map file into memory (MAP_SHARED so changes reflected in file) */
   m_base = mmap(NULL, m_size, prot, MAP_SHARED, fd, 0);
   if (m_base == MAP_FAILED) {
      return NULL;
   }
   
   /* alloc & init MYFILE struct */
   if ((file = malloc(sizeof(MYFILE))) == NULL) {
      /* unmap memory (but save _errno_ in case munmap changes it) */
      int malloc_errno = errno;
      munmap(m_base, m_size);
      errno = malloc_errno;
      return NULL;
   }
   file->f_fd = fd;
   file->f_size = f_size;
   file->f_flags = flags;
   file->m_rwp = file->m_base = m_base;
   file->m_size = m_size;
   
   return file;
}

/* myclose()
 * DESC: close file opened with myopen()
 * ARGS:
 *  - file: pointer to MYFILE struct
 * RETV: returns 0 upon success, -1 upon error.
 */
int myclose(MYFILE *file) {
   int retv = 0;
   
   /* resize file if writable */
   if (myfile_writeable(file) && ftruncate(file->f_fd, file->f_size) < 0) {
      retv = -1;
   }
   
   /* unmap memory */
   if (munmap(file->m_base, file->m_size) < 0) {
      retv = -1;
   }
   
   /* close file */
   if (close(file->f_fd) < 0) {
      retv = -1;
   }

   free(file);
   return retv;
}

/* myread()
 * DESC: read in _count_ bytes into _buf_.
 * ARGS:
 *  - file: MYFILE pointer
 *  - buf: pointer to beginning of buffer
 *  - count: number of bytes to read
 * RETV: returns _count_ upon success; returns -1 upon error.
*/
ssize_t myread(MYFILE *file, void *buf, size_t count) {
   size_t f_rembytes;
   
   /* check file permissions */
   if (!myfile_readable(file)) {
      /* lack read permissions */
      errno = EBADF;
      return -1;
   }

   /* copy file contents to buffer */
   f_rembytes = myfile_f_rembytes(file);
   count = (count < f_rembytes) ? count : f_rembytes;
   memcpy(buf, file->m_rwp, count);

   /* update file offset */
   file->m_rwp = (char *) file->m_rwp + count;
   
   return count;
}


/* mywrite()
 * DESC: write _count_ bytes from _buf_ into file.
 * ARGS:
 *  - file: MYFILE pointer
 *  - buf: pointer to beginning of source buffer
 *  - count: number of bytes to write
 * RETV: returns _count_ upon success; returns -1 upon error.
 */
ssize_t mywrite(MYFILE *file, const void *buf, size_t count) {
   size_t m_rembytes, offset;
   
   /* check file permissions */
   if (!myfile_writeable(file)) {
      /* lack write permissions */
      errno = EBADF;
      return -1;
   }

   /* move offset to end of file if appending */
   if ((file->f_flags & O_APPEND)) {
      if (myseek(file, 0, SEEK_END) < 0) {
         return -1;
      }
   }
   
   /* check mmap size */
   m_rembytes = myfile_m_rembytes(file);
   if (m_rembytes < count) {
      size_t m_newsize, m_incsize;
      
      /* increase mapped memory size */
      m_incsize = PAGE_SIZE;
      m_newsize = file->m_size + ((m_incsize < count - m_rembytes) ?
                                  count - m_rembytes : m_incsize);
      if (mytruncate(file, file->f_size, m_newsize) < 0) {
         return -1;
      }
   }
   
   /* copy buffer contents to file */
   memcpy(file->m_rwp, buf, count);
   
   /* update file fields after write */
   file->m_rwp = (char *) file->m_rwp + count;
   if ((offset = myfile_offset(file)) > file->f_size) {
      file->f_size = offset;
   }
   
   return count;
}

/* myseek()
 * DESC: seek to offset in file.
 * ARGS:
 *  - file: MYFILE pointer
 *  - offset: offset relative to reference position specified by _whence_
 *  - whence: reference position (SEEK_SET, SEEK_CUR, SEEK_END).
 * RETV: returns absolute offset from beginning of file upon success;
 *       returns -1 upon error.
*/
off_t myseek(MYFILE *file, off_t offset, int whence) {
   off_t absoff; // absolute offset from beginning of file
   off_t baseoff; // base offset (depends on _whence_)

   switch (whence) {
   case SEEK_SET:
      baseoff = 0; // from beginning offset, which is 0
      break;
   case SEEK_CUR:
      baseoff = myfile_offset(file); // from current offset
      break;
   case SEEK_END:
      baseoff = file->f_size; // from end of file
      break;
   default:
      errno = EINVAL;
      return -1;
   }

   /* check for overflow/underflow
    * NOTE: the (absolute value of the) sum of two integral values
    *       is always less than (the absolute value of) either summand
    *       if integer overflow occurred
    */
   if (chk_overflow_add(baseoff, offset)) {
      errno = EOVERFLOW;
      return -1;
   }
   /* compute new (absolute) offset */
   absoff = baseoff + offset;

   /* check bounds of new offset */
   if (absoff < 0 ) {
      errno = EINVAL;
      return -1;
   }
   if (absoff > file->f_size) {
      /* resize file for seek past end */
      if (mytruncate(file, absoff, -1) < 0) {
         return -1;
      }
   }
   /* check overflow again (this time both summands are positive, so can simplify check */
   if ((char *) file->m_base + absoff < (char *) file->m_base) {
      errno = EOVERFLOW;
      return -1;
   }

   /* update file fields */
   file->m_rwp = (char *) file->m_base + absoff;
   
   return absoff;
}

/* myflush()
 * DESC: commits changes to filesystem
 * ARGS:
 *  - file: MYFILE pointer
 * RETV: returns 0 upon success; returns -1 upon failure
 */
int myflush(MYFILE *file) {
   if (msync(file->m_base, file->m_size, MS_SYNC) < 0) {
      return -1;
   }
   return 0;
}

/* mytruncate()
 * DESC: resizes memory-mapped MYFILE.
 * ARGS:
 *  - file: MYFILE pointer
 *  - f_newsize: new size of file (-1 means leave it alone).
 *  - m_newsize: new size of file's mapped memory (-1 means adjust according
 *               to f_newsize). Note: cannot be smaller than f_newsize.
 * RETV: returns 0 upon success; returns -1 upon failure.
 */
int mytruncate(MYFILE *file, ssize_t f_newsize, ssize_t m_newsize) {
   void *m_newbase;

   /* compute new file/memory sizes, if necessary */
   if (f_newsize < 0 && m_newsize < 0) {
      /* nothing to do */
      return 0;
   }
   if (f_newsize < 0) {
      /* don't modify file size */
      f_newsize = file->f_size;
   }
   if (m_newsize < 0) {
      /* automatically adjust memory size */
      m_newsize = (f_newsize < file->m_size) ? file->m_size : page_round_plus1(f_newsize);
   }
   if (m_newsize < f_newsize) {
      /* memory map must be at least as large as file size */
      errno = EINVAL;
      return -1;
   }
   
   /* resize file (note: do this first, in case it fails) */
   if (ftruncate(file->f_fd, m_newsize) < 0) {
      return -1;
   }
   
   /* remap file (note: do this only after file has been resized) */
   m_newbase = mremap(file->m_base, file->m_size, m_newsize, MREMAP_MAYMOVE);
   if (m_newbase == MAP_FAILED) {
      /* try to resize file back to original size, as not to leave file in bad state
       * (if this doesn't work, we're in a real jam) */
      if (ftruncate(file->f_fd, file->m_size) < 0) {
         return -1; // damn
      }
      return -1;
   }

   /* update file's memory fields */
   file->m_size = m_newsize;
   file->m_rwp = (char *) m_newbase + myfile_offset(file);
   file->m_base = m_newbase;

   return 0;
}




/////////// UTILITY FUNCTIONS ////////////
/* memory mapping */
size_t page_round_plus1(size_t size) {
   return (size/PAGE_SIZE + 1) * PAGE_SIZE;
}

/* MYFILE functions */
int myfile_readable(MYFILE *file) {
   int access_flags = file->f_flags & MYFILE_ACCESS_MASK;
   return access_flags == O_RDONLY || access_flags == O_RDWR;
}
int myfile_writeable(MYFILE *file) {
   return file->f_flags & (O_WRONLY | O_RDWR);
}
off_t myfile_offset(MYFILE *file) {
   return (char *) file->m_rwp - (char *) file->m_base;
}
off_t myfile_f_rembytes(MYFILE *file) {
   return file->f_size - myfile_offset(file);
}
off_t myfile_m_rembytes(MYFILE *file) {
   return file->m_size - myfile_offset(file);
}


/* arithmetic functions */
int oabs(off_t offset) {
   return (offset < 0) ? -offset : offset;
}
int chk_overflow_add(off_t val1, off_t val2) {
   /* if val1 and val2 have opposite signs, then overflow never occurs */
   if ((val1 < 0) ^ (val2 < 0)) {
      return 0;
   }
   /* otherwise, consider absolute values */
   return oabs(val1 + val2) < oabs(val1) ? 1 : 0;
}
int chk_overflow_sub(off_t val1, off_t val2) {
   return chk_overflow_sub(val1, -val2);
}

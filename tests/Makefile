.SUFFIXES:

CLANG = clang
LLVMFLAGS = -emit-llvm

SRCS = $(wildcard *.c)
OBJS = $(SRCS:.c=.ll)

.PHONY: all
all: $(OBJS)

%.ll: %.c
	$(CLANG) $(LLVMFLAGS) -S -o $@ $<

test%: test%.ll
	true

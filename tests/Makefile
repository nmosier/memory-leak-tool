.SUFFIXES:

CLANG = clang
LLVMFLAGS = -emit-llvm

%.ll: %.c
	$(CLANG) $(LLVMFLAGS) -S -o $@ $<

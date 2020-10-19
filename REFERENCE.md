LLVM-IR
- [LLVM-IR Specification](http://llvm.org/docs/LangRef.html)
- To emit LLVM-IR using clang,
  `clang -S -emit-llvm name -o <outfile> <infile>`
- [LLVM Libraries](https://releases.llvm.org/1.8/docs/UsingLibraries.html)
  It sounds like the `LLVMAsmParser.o` library might be useful for parsing LLVM-IR.
- We might want to use (llvmpy)[http://www.llvmpy.org/llvmpy-doc/0.12.7/doc] for manipulating LLVM-IR.

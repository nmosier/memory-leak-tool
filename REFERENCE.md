LLVM-IR
- [LLVM-IR Specification](http://llvm.org/docs/LangRef.html)
- To emit LLVM-IR using clang,
  `clang -S -emit-llvm name -o <outfile> <infile>`
- We might want to use (llvmpy)[http://www.llvmpy.org/llvmpy-doc/0.12.7/doc] for manipulating LLVM-IR. Use `llvm.core.Module.from_assembly(path: str)` to parse .ll assembly.

SMT
- If we use llvmpy, then we could also use PySMT.


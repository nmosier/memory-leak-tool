# memory-leak-tool

## Installation
### MacOS
1. Install PySMT: `pip3 install pysmt`
1. Install a solver backend for PySMT, e.g. MathSAT: `pysmt-install --msat`
1. Install LLVM 9: `brew install llvm@9`
1. Install llvmlite: `pip3 install llvmlite`
1. Clone this repository: `git clone https://github.com/nmosier/memory-leak-tool.git`

## Getting Started
To test out the tool on a test program `test3.c`:
```
cd tests
make
cd ../src
./main.py ../tests/test3.ll
```
## References
- [LLVM IR Reference Manual](https://llvm.org/docs/LangRef.html)
- [llvmlite Documentation](https://llvmlite.readthedocs.io/en/latest/index.html)
- [pysmt Documentation](https://pysmt.readthedocs.io/en/latest/)

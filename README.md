# memory-leak-tool

## Installation
### MacOS
1. Install PySMT: `pip3 install pysmt`
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

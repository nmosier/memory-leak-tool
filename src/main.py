#!/usr/local/bin/python3

from llvmlite import binding as llvm
from llvmlite import ir as lc
import sys

def usage(file=sys.stdout):
    print("usage: {} <ll-asm-file>".format(sys.argv[0]), file=file)

if len(sys.argv) != 2:
    usage(sys.stderr)
    sys.exit(1)

llvm.initialize()
llvm.initialize_native_target()
llvm.initialize_native_asmprinter()

    
ll_path = sys.argv[1]
ll_file = open(ll_path, "r")
ll_contents = ll_file.read()
ll_file.close()

module = llvm.parse_assembly(ll_contents)
module.verify()

# only examine functions that are defined
function_defs = filter(lambda fn: not fn.is_declaration, module.functions)

for fn in function_defs:
    print(fn)

    print("basic blocks:")
    for blk in fn.blocks:
        print(blk)
    


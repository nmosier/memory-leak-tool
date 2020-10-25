#!/usr/local/bin/python3

from llvmlite import binding as llvm
from llvmlite import ir as lc
import sys
import re

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
function_defs = list(filter(lambda fn: not fn.is_declaration, module.functions))

# returns tuple of malloc calls and free calls
def find_calls(fn):
    malloc_calls = []
    free_calls = []
    for blk in fn.blocks:
        for inst in blk.instructions:
            if inst.opcode == "call":
                for op in inst.operands:
                    if op.name == "malloc":
                        malloc_calls.append(inst)
                    elif op.name == "free":
                        free_calls.append(inst)
    return (malloc_calls, free_calls)
                        


for fn in function_defs:
    (malloc_calls, free_calls) = find_calls(fn)
    print("malloc calls in function {}:".format(fn.name))
    for inst in malloc_calls:
        print(inst)
    print("free calls in function {}:".format(fn.name))
    for inst in free_calls:
        print(inst)

for fn in function_defs:
    for blk in fn.blocks:
        print(blk)



for block in list(function_defs)[0].blocks:
        # get last instruction of current block
        cur_inst = list(block.instructions)[-1]
        print("Inst:", cur_inst)
        if cur_inst.opcode in ["br", "switch"]:
            for operand in cur_inst.operands:
                print("Operand:", operand)
                print("Attributes:")
                for attribute in operand.attributes:
                    print(attribute)
                print("Type:", operand.type)

# get list of blocks that directly precede this block
def predecessor_blocks(successor):
    blocks = []
    for block in successor.function.blocks:
        last_inst = list(block.instructions)[-1]
        if last_inst.opcode in ["br", "switch"]:
            for operand in last_inst.operands:
                if operand == successor:
                    blocks.append(block)
    return blocks

def block_get_desc(block) -> str:
    lines = str(block).split('\n')
    for line in lines:
        if re.match(r'\d+:\s+; preds = ', line):
            return line
    return None

def block_get_id(block) -> int:
    line = block_get_desc(block)
    if line:
        return int(re.match(r'\d+', line).group())
    else:
        return 1

def block_get_pred_ids(block):
    line = block_get_desc(block)
    if line:
        block_strs = re.findall(r'%\d+', line)
        return list(map(lambda block_str: int(block_str[1:]), block_strs))
    else:
        return list()

def block_id_to_block(block_id: int, fn):
    for blk in fn.blocks:
        if block_get_id(blk) == block_id:
            return blk
    return None
    
def block_get_preds(block, fn):
    return list(map(lambda block_id: block_id_to_block(block_id, fn), block_get_pred_ids(block)))

first_func = list(function_defs)[0]
last_block = list(first_func.blocks)[-1]
print("Predecessor blocks of last block: ");
for block in predecessor_blocks(last_block):
    print(block)


for fn in function_defs:
    for blk in fn.blocks:
        print("block id = {}".format(block_get_id(blk)))
        print("block preds = ", block_get_preds(blk, fn))

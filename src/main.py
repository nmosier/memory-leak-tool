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
    
def block_get_preds(block):
    return list(map(lambda block_id: block_id_to_block(block_id, block.function), block_get_pred_ids(block)))

def function_get_pred_graph(fn):
    graph = dict()
    for block in fn.blocks:
        graph[block] = block_get_preds(block)
    return graph

def print_pred_graph_at_block(pred_graph, block):
    # TODO
    return

def pred_graph_get_paths_to_block(pred_graph, block, prefix=list()):
    prefix = prefix + [block]
    if len(pred_graph[block]) == 0:
        # reached start block
        return [prefix[::-1]];
    else:
        paths = list()
        for pred_block in pred_graph[block]:
            paths.extend(pred_graph_get_paths_to_block(pred_graph, pred_block, prefix))
        return paths

def block_get_transitions(block):
    # get last instruction
    last_inst = list(block.instructions)[-1]
    last_inst_str = str(last_inst)
    if last_inst.opcode != "br":
        return {}
    operands = re.findall(r'%\w+', last_inst_str)
    if re.match(r'\s*br label', last_inst_str):
        assert len(operands) == 1
        return {operands[0]: 'T'}
    elif re.match(r'\s*br i1', last_inst_str):
        return {operands[1]: '{} != 0'.format(operands[0]),
                operands[2]: '{} == 0'.format(operands[0])}
    else:
        assert(False)

def path_get_constraints(path):
    constraints = []
    prev_block = path[0]
    for i in range(1, len(path)):
        cur_block = path[i]
        transitions = block_get_transitions(prev_block)
        key = '%' + str(block_get_id(cur_block))
        constraints.append(transitions[key])
        prev_block = path[i]
    return constraints
    
for fn in function_defs:
    for blk in fn.blocks:
        print("block id = {}".format(block_get_id(blk)))
        print("block preds = ", block_get_preds(blk))

for fn in function_defs:
    (mallocs, frees) = find_calls(fn)
    print("frees:")
    for free in frees:
        print(free)
        print(block_get_pred_ids(free.block))
        print("pred graph begin")
        pred_graph = function_get_pred_graph(fn)
        paths = pred_graph_get_paths_to_block(pred_graph, free.block)
        for path in paths:
            print(path_get_constraints(path))
        print("pred graph end")

print("block transitions:")
for fn in function_defs:
    for blk in fn.blocks:
        print("block:", blk)
        print("transitions:", block_get_transitions(blk))

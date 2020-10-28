#!/usr/local/bin/python3

from llvmlite import binding as llvm
from llvmlite import ir as lc
from pysmt.shortcuts import *
from pysmt.typing import *
import sys
import re

class Block:
    def __init__(self, llvm_blk: llvm.ValueRef):
        assert llvm_blk.is_block

        self.llvm_blk = llvm_blk
        
        desc = Block.get_desc(llvm_blk)
        self.name = Block.get_name(desc)
        self.pred_names = Block.get_pred_names(desc)
        self.transitions = Block.get_transitions(llvm_blk)

    @staticmethod
    def get_desc(llvm_blk: llvm.ValueRef) -> str:
        lines = str(llvm_blk).split('\n')
        for line in lines:
            if re.match(r'\d+:\s+; preds = ', line):
                return line
        return None
        
    @staticmethod
    def get_name(desc: str) -> str:
        if desc == None:
            return '1'
        else:
            return re.match(r'\d+', desc).group()

    @staticmethod
    def get_pred_names(desc: str) -> list:
        if desc:
            names = re.findall(r'%d+', desc)
            return list(map(lambda name: name[1:], names[1:]))
        else:
            return list()

    @staticmethod
    def get_transitions(llvm_blk: llvm.ValueRef) -> dict:
        last_inst = list(llvm_blk.instructions)[-1]
        last_inst_str = str(last_inst)
        if last_inst.opcode != "br":
            return {}
        operands = list(map(lambda s: s[1:], re.findall(r'%\w+', last_inst_str)))
        if re.match(r'\s*br label', last_inst_str):
            assert len(operands) == 1
            return {operands[0]: 'T'}
        elif re.match(r'\s*br i1', last_inst_str):
            return {operands[1]: 'v{} != 0'.format(operands[0]),
                    operands[2]: 'v{} == 0'.format(operands[0])}
        else:
            assert(False)

            
class Path:
    def __init__(self, blk_list: list):
        self.blk_list = blk_list
        self.constraints = Path.get_constraints(blk_list)

    @staticmethod
    def get_constraints(blk_list):
        constraints = []
        prev_block = path[0]
        for i in range(1, len(path)):
            cur_block = path[i]
            transitions = prev_block.transitions
            key = cur_block.name
            constraints.append(transitions[key])
            prev_block = path[i]
        return constraints
    
class Function:
    def __init__(self, llvm_fn: llvm.ValueRef):
        assert(llvm_fn.is_function)
        self.llvm_fn = llvm_fn
        self.blocks = list(map(lambda llvm_blk: Block(llvm_blk), llvm_fn.blocks))
        self.blkname_to_block_map = map(lambda block: (block.name, block), self.blocks)
        self.pred_graph = self.get_pred_graph()

    def __str__(self):
        return str(self.llvm_fn)
        
    def blkname_to_block(self, blkname: str) -> Block:
        return self.blkname_to_block_map[blkname]

    def get_block_preds(self, block: Block) -> list:
        return list(map(lambda blkname: self.blkname_to_block(blkname), block.pred_names))

    def get_pred_graph(self) -> dict:
        return dict(map(lambda block: (block, self.get_block_preds(block)), self.blocks))
        
    def get_paths_to_block(self, block, prefix=list()) -> list:
        prefix = prefix + [block]
        if len(self.pred_graph[block]) == 0:
            # base case: reached start block
            return [prefix[::-1]];
        else:
            # recursive case 
            paths = list()
            for pred_block in pred_graph[block]:
                paths.extend(pred_graph_get_paths_to_block(pred_graph, pred_block, prefix))
            return paths

    def get_calls(self, name: str) -> list:
        calls = []
        for block in self.blocks:
            for inst in block.llvm_blk.instructions:
                if inst.opcode == 'call':
                    op1 = list(inst.operands)[0]
                    if op1.name == name:
                        calls.append(inst)
        return calls

class Module:
    def __init__(self, llvm_module: llvm.ModuleRef):
        self.llvm_module = llvm_module
        llvm_fn_defs = filter(lambda llvm_fn: not llvm_fn.is_declaration, llvm_module.functions)
        self.function_definitions = list(map(lambda llvm_fn: Function(llvm_fn), llvm_fn_defs))

    @staticmethod
    def parse_file(path: str):
        f = open(path, 'r')
        contents = f.read()
        f.close()
        llvm_module = llvm.parse_assembly(contents)
        llvm_module.verify()
        return Module(llvm_module)


def usage(file=sys.stdout):
    print("usage: {} <ll-asm-file>".format(sys.argv[0]), file=file)

if len(sys.argv) != 2:
    usage(sys.stderr)
    sys.exit(1)

llvm.initialize()
llvm.initialize_native_target()
llvm.initialize_native_asmprinter()

ll_path = sys.argv[1]

module = Module.parse_file(ll_path)

print('function definitions:')
for fn in module.function_definitions:
    print(fn)


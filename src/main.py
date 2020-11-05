#!/usr/local/bin/python3

from llvmlite import binding as llvm
from llvmlite import ir as lc
from pysmt.shortcuts import *
from pysmt.typing import *
import sys
import re


class Variable:
    target_data = llvm.create_target_data('')
    
    def __init__(self, llvm_inst: llvm.ValueRef, name: str, smt_type: PySMTType):
        self.llvm_inst = llvm_inst
        self.name = name
        self.smt_type = smt_type
        self.symbol = Symbol('v_' + self.name, self.smt_type)

    def __str__(self) -> str:
        return self.name

    @staticmethod
    def get_type_from_inst(llvm_inst: llvm.ValueRef) -> PySMTType:
        llvm_type = llvm_inst.type
        if llvm_type.is_pointer:
            return BVType(Variable.target_data.get_abi_size(llvm_type) * 8)
        else:
            llvm_type_s = str(llvm_type)
            match = re.match('i\d+', llvm_type_s)
            assert match != None
            bits_str = match.group(0)[1:]
            bits = int(bits_str)
            if bits == 1:
                return BOOL
            else:
                return BVType(bits)
                
    @staticmethod
    def from_inst(llvm_inst: llvm.ValueRef):
        assert llvm_inst.is_instruction
        inst_str = str(llvm_inst)
        padded_assign = re.match('\s+%\w+', inst_str)
        if padded_assign == None:
            return None
        else:
            padded_assign_str = padded_assign.group(0)
            assign = padded_assign_str[padded_assign_str.find('%') + 1 : ]
            return Variable(llvm_inst, assign, Variable.get_type_from_inst(llvm_inst))

    # returns formula
    def get_def_constraint(self, var_dict: dict):
        # handler of signature (opcodes) -> formula
        # handler = {'icmp': lambda 
        inst = self.llvm_inst
        opcode = inst.opcode
        if opcode == 'icmp':
            for operand in inst.operands:
                print('operand:', operand)
        


class Block:
    def __init__(self, llvm_blk: llvm.ValueRef, variables_dict: dict):
        assert llvm_blk.is_block
        self.llvm_blk = llvm_blk
        desc = Block.get_desc(llvm_blk)
        self.name = Block.get_name(desc)
        self.pred_names = Block.get_pred_names(desc)
        self.transitions = Block.get_transitions(llvm_blk, variables_dict)

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
        if desc != None:
            names = re.findall(r'%\d+', desc)
            return list(map(lambda name: name[1:], names))
        else:
            return list()

    @staticmethod
    def get_transitions(llvm_blk: llvm.ValueRef, variables_dict: dict) -> dict:
        last_inst = list(llvm_blk.instructions)[-1]
        last_inst_str = str(last_inst)
        if last_inst.opcode != "br":
            return {}
        operands = list(map(lambda s: s[1:], re.findall(r'%\w+', last_inst_str)))
        if re.match(r'\s*br label', last_inst_str):
            assert len(operands) == 1
            return {operands[0]: TRUE()}
        elif re.match(r'\s*br i1', last_inst_str):
            var = variables_dict[operands[0]]
            assert var.smt_type == BOOL
            return {operands[1]: var.symbol,
                    operands[2]: Not(var.symbol)}
        else:
            assert(False)

            
class Path:
    def __init__(self, blk_list: list):
        self.blk_list = blk_list
        self.constraints = Path.get_constraints(blk_list)
        
    def __str__(self):
        blknames = map(lambda blk: blk.name, self.blk_list)
        blkstr = ' -> '.join(blknames)
        constraint_str = str(self.constraints)
        return '({}, {})'.format(blkstr, constraint_str)

    @staticmethod
    def get_constraints(path: list) -> pysmt.formula:
        constraints = []
        prev_block = path[0]
        for i in range(1, len(path)):
            cur_block = path[i]
            transitions = prev_block.transitions
            key = cur_block.name
            constraints.append(transitions[key])
            prev_block = path[i]

        return And(*constraints)

    def __contains__(self, val) -> bool:
        if type(val) == Block:
            return self.contains_block(val)
        else:
            assert False
     
    def contains_block(self, block: Block) -> bool:
        return block in self.blk_list

    def free_variables(self, fn: Function) -> list:
        return list(map(lambda var: fn.pysmtsym_to_variable(var),
                        self.constraints.get_free_variables()))
        
class Function:
    def __init__(self, llvm_fn: llvm.ValueRef):
        assert(llvm_fn.is_function)
        self.variables = Function.get_variables(llvm_fn)
        self.variables_dict = dict(map(lambda var: (var.name, var), self.variables))
        self.llvm_fn = llvm_fn
        self.blocks = list(map(lambda llvm_blk: Block(llvm_blk, self.variables_dict),
                               llvm_fn.blocks))
        self.blkname_to_block_dict = dict(map(lambda block: (block.name, block), self.blocks))
        self.llvmblk_to_block_dict = dict(map(lambda block: (block.llvm_blk, block), self.blocks))
        self.pred_graph = self.get_pred_graph()
        self.symbol_to_var_dict = dict(map(lambda var: (var.symbol, var), self.variables))

    def __str__(self):
        return str(self.llvm_fn)
        
    def blkname_to_block(self, blkname: str) -> Block:
        return self.blkname_to_block_dict[blkname]

    def llvmblk_to_block(self, llvmblk: llvm.ValueRef) -> Block:
        assert llvmblk.is_block
        return self.llvmblk_to_block_dict[llvmblk]

    def get_block_preds(self, block: Block) -> list:
        return list(map(lambda blkname: self.blkname_to_block(blkname), block.pred_names))

    def get_pred_graph(self) -> dict:
        return dict(map(lambda block: (block, self.get_block_preds(block)), self.blocks))
        
    def get_paths_to_block(self, block, prefix=list()) -> list:
        prefix = prefix + [block]
        if len(self.pred_graph[block]) == 0:
            # base case: reached start block
            return [Path(prefix[::-1])]
        else:
            # recursive case 
            paths = list()
            for pred_block in self.pred_graph[block]:
                paths.extend(self.get_paths_to_block(pred_block, prefix))
            return paths

    def get_calls(self, name: str) -> list:
        calls = []
        for block in self.blocks:
            for inst in block.llvm_blk.instructions:
                if inst.opcode == 'call':
                    op1 = list(inst.operands)[1]
                    if op1.name == name:
                        calls.append(inst)
        return calls

    @staticmethod
    def get_variables(llvm_fn: llvm.ValueRef) -> list:
        variables = [] 
        for llvm_blk in llvm_fn.blocks:
            for llvm_inst in llvm_blk.instructions:
                var = Variable.from_inst(llvm_inst)
                if var != None:
                    variables.append(var)
        return variables

    def get_variable(self, name: str) -> Variable:
        return self.variables_dict[name]

    def pysmtsym_to_variable(self, pysmtsym: Symbol) -> Variable:
        return self.symbol_to_var_dict[pysmtsym]

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

llvm.initialize()
llvm.initialize_native_target()
llvm.initialize_native_asmprinter()

if len(sys.argv) != 2:
    usage(sys.stderr)
    sys.exit(1)
ll_path = sys.argv[1]
module = Module.parse_file(ll_path)

for fn in module.function_definitions:
    mallocs = fn.get_calls('malloc')
    frees = fn.get_calls('free')

    assert len(mallocs) == 1
    assert len(frees) == 1

    malloc = mallocs[0]
    free = frees[0]

    malloc_blk = fn.llvmblk_to_block(malloc.block)
    free_blk = fn.llvmblk_to_block(free.block)
    
    # find frees without corresponding mallocs
    paths = filter(lambda path: malloc_blk in path, fn.get_paths_to_block(free_blk))
    path_constraints = map(lambda path: path.constraints, paths)
    formula = Or(*path_constraints)
    print(formula)

    free_vars = list(map(fn.pysmtsym_to_variable, formula.get_free_variables()))
    print('free variables:');
    for var in free_vars:
        print(var)

    print(list(map(lambda var: str(var), fn.variables)))

    # TEST
    print('def constraint:', fn.get_variable('6').get_def_constraint(None))
    
        
    with Solver() as solver:
        solver.add_assertion(formula)
        res = solver.solve()
        if res:
            print('SAT')
            # print_solution(solver.get_model())
            print(solver.get_model())
        else:
            print('UNSAT')


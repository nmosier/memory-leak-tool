#!/usr/local/bin/python3

from llvmlite import binding as llvm
from llvmlite import ir as lc
from pysmt.shortcuts import *
from pysmt.typing import *
import re
import argparse
from enum import Enum, auto
from copy import copy

class Module:
    def __init__(self, llvm_module: llvm.ModuleRef):
        self.llvm_module = llvm_module

        # first create global variables
        str2var = dict()
        for llvm_fn in llvm_module.functions:
            str2var[str(llvm_fn)] = Variable.from_func(llvm_fn)
        assert len(list(llvm_module.global_variables)) == 0
        
        self.function_definitions = list(map(lambda llvm_fn: Function(llvm_fn, str2var),
                                             filter(lambda llvm_fn: not llvm_fn.is_declaration,
                                                    llvm_module.functions)))

        # global str2var: only includes global declarations/definitions
        # str2var = list(map(lambda llvm_fn: (str(llvm_fn) 

    @staticmethod
    def parse_file(path: str):
        f = open(path, 'r')
        contents = f.read()
        f.close()
        llvm_module = llvm.parse_assembly(contents)
        llvm_module.verify()
        return Module(llvm_module)

class Value:
    def __init__(self, llvm_val: llvm.ValueRef):
        self.llvm_val = llvm_val

class Function(Value):
    def __init__(self, llvm_fn: llvm.ValueRef, str2var: dict):
        Value.__init__(self, llvm_fn)

        # construction str -> variable map
        str2var = copy(str2var)
        ## instructions
        for llvm_blk in llvm_fn.blocks:
            for llvm_inst in llvm_blk.instructions:
                llvm_inst_str = str(llvm_inst)
                if re.match('\s*%\w+\s*=', llvm_inst_str):
                    var = Variable.from_inst(llvm_inst)
                    str2var[llvm_inst_str] = var
        ## arguments
        for llvm_arg in llvm_fn.arguments:
            str2var[str(llvm_arg)] = Variable.from_arg(llvm_arg)
        
        # blocks
        ## construct str -> block map
        self.blocks = list(map(lambda llvm_blk: Block(llvm_blk, str2var), llvm_fn.blocks))
        str2blk = dict(map(lambda blk: (str(blk.llvm_val), blk), self.blocks))
        
        # arguments
        self.arguments = list(map(lambda llvm_arg: str2var[str(llvm_arg)], llvm_fn.arguments))

        # more initialization
        for blk in self.blocks:
            blk.init1(str2var, str2blk)
        
        # set block predecessors
        for blk in self.blocks:
            for successor in blk.successors.keys():
                successor.predecessors.append(blk)
        
        ## TODO
        
class Variable(Value):
    def __init__(self, llvm_val: llvm.ValueRef, name: str):
        Value.__init__(self, llvm_val)
        self.name = name
        self.type = Type(llvm_val.type)
        self.symbol = Symbol('v_' + self.name, self.type.pysmt_type)
        print('created variable {}'.format(self.symbol))

    @staticmethod
    def from_inst(llvm_inst: llvm.ValueRef):
        # name
        llvm_inst_str = str(llvm_inst)
        full_name = re.search('%\w+', llvm_inst_str).group(0)
        name = full_name[1:]
        return Variable(llvm_inst, name)

    @staticmethod
    def from_arg(llvm_arg: llvm.ValueRef):
        # name
        llvm_arg_str = str(llvm_arg)
        name = llvm_arg_str.split()[1][1:]
        return Variable(llvm_arg, name)

    # works with both declarations and definitions
    @staticmethod
    def from_func(llvm_decl: llvm.ValueRef):
        # TODO: possible name collisions with global variables
        return Variable(llvm_decl, llvm_decl.name)
    
class Immediate(Value):
    def __init__(self, llvm_op: llvm.ValueRef):
        Value.__init__(self, llvm_op)
        llvm_op_str = str(llvm_op)
        print('Immediate:', llvm_op_str)
        val_str = llvm_op_str.split()[1]
        if val_str == 'null':
            self.imm = 0
        else:
            self.imm = int(llvm_op_str.split()[1])
        self.type = Type(llvm_op.type)
        self.pysmt_formula = self._get_pysmt_formula()

    def _get_pysmt_formula(self):
        if self.type.pysmt_type.is_bool_type():
            m = {0: FALSE, 1: TRUE}
            return m[self.imm]
        elif self.type.pysmt_type.is_bv_type():
            return BV(self.imm, self.type.pysmt_type.width)
        else:
            assert False
        
class Operand(Value):
    # TODO: enumeration of possibilities
    class Kind(Enum):
        VARIABLE = auto()
        IMMEDIATE = auto()
        BLOCK = auto()
    
    def __init__(self, llvm_op: llvm.ValueRef, str2var: dict, str2blk: dict):
        Value.__init__(self, llvm_op)
        llvm_op_str = str(llvm_op)
        self.kind = None
        self.value = None
        
        if llvm_op_str in str2var:
            # is variable
            self.kind = Operand.Kind.VARIABLE
            self.value = str2var[llvm_op_str]
        elif llvm_op_str in str2blk:
            # is block
            self.kind = Operand.Kind.BLOCK
            self.value = str2blk[llvm_op_str]
        else:
            # is immediate
            self.kind = Operand.Kind.IMMEDIATE
            self.value = Immediate(llvm_op)

    def formula(self, assignments: dict) -> pysmt.formula:
        if self.kind == Operand.Kind.VARIABLE:
            print('formula:', self.value.llvm_val)
            return assignments[self.value]
        elif self.kind == Operand.Kind.IMMEDIATE:
            return self.value.pysmt_formula
        else:
            assert False

class Instruction(Value):
    def __init__(self, llvm_inst: llvm.ValueRef, str2var: dict, str2blk: dict):
        Value.__init__(self, llvm_inst)
        self.opcode = llvm_inst.opcode
        llvm_inst_str = str(llvm_inst)
        self.toks = llvm_inst_str.split()
        if llvm_inst_str in str2var:
            # is variable definition
            self.is_variable_definition = True
            self.defined_variable = str2var[llvm_inst_str]
        else:
            self.is_variable_definition = False
            self.defined_variable = None

        # operands
        self.operands = list(map(lambda llvm_op: Operand(llvm_op, str2var, str2blk),
                                 self.llvm_val.operands))

    # path: dictionary from blocks -> info
    # assignments: dictionary from Variable -> pysmt.formula
    def apply(self, path: list, assignments: dict, store):
        d = {'store': self._store,
             'icmp':  self._icmp,
             'load':  self._load,
             'phi':   self._phi,
             'alloca':self._alloca,
             }
        d[self.opcode](path, assignments, store)
        
    def _store(self, path: list, assignments: dict, store):
        dst = self.operands[1]
        val = self.operands[0]
        assert dst.value.type.is_pointer
        store.store(dst.value, val.formula(assignments))

    def _load(self, path: list, assignments: dict, store):
        src = self.operands[0]
        assert src.kind == Operand.Kind.VARIABLE
        load_formula = store.load(src.value)
        print('load_formula:', load_formula)
        def_formula = Equals(self.defined_variable.symbol, load_formula)
        assignments[self.defined_variable] = load_formula
        path[-1][1].append(def_formula)

    def _alloca(self, path: list, assigments: dict, store):
        assignments[self.defined_variable] = TRUE()
        store.alloc(self.defined_variable)

    def _icmp(self, path: list, assignments: dict, store):
        cond = self.toks[3]
        formulas = {'eq': Equals,
                    'ne': NotEquals,
                    'ugt': BVUGT,
                    'uge': BVUGE,
                    'ult': BVULT,
                    'ule': BVULE,
                    'sgt': BVSGT,
                    'sge': BVSGE,
                    'slt': BVSLT,
                    'sle': BVSLE
        }
        atoms = list(map(lambda op: op.formula(assignments), self.operands))
        icmp_formula = formulas[cond](*atoms)
        def_formula = Iff(icmp_formula, self.defined_variable.symbol)
        assignments[self.defined_variable] = icmp_formula
        path[-1][1].append(def_formula)

    def _phi(self, path: list, assignments: dict, store):
        # find branches (2nd of pairs)
        labels = re.findall('%\w+\s*\]', str(self.llvm_val))
        labels = list(map(lambda label: re.findall('\w+', label), labels))
        # get blocks from labels
        assert len(labels) == len(self.operands)
        for (op, label) in zip(self.operands, labels):
            if label == path[-1][0].name:
                def_formula = Equals(op.formula(assignments), self.symbol)
                path[-1][1].append(def_formula)
                break
                
class Block(Value):
    def __init__(self, llvm_blk: llvm.ValueRef, str2var: dict):
        Value.__init__(self, llvm_blk)
        self.predecessors = list() # populated later
        # set the name
        re_name = re.match('\d+', str(llvm_blk))
        if re_name == None:
            self.name = str(len(list(llvm_blk.function.arguments)))
        else:
            self.name = re_name
        
    def init1(self, str2var: dict, str2blk: dict):
        self.successors = Block._get_successors(self.llvm_val, str2var, str2blk)
        self.instructions = list(map(lambda llvm_inst: Instruction(llvm_inst, str2var, str2blk),
                                     self.llvm_val.instructions))

    @staticmethod
    def _get_successors(llvm_blk: llvm.ValueRef, str2var: dict, str2blk: dict) -> dict:
        last_inst = list(llvm_blk.instructions)[-1]
        last_inst_str = str(last_inst)
        if last_inst.opcode != "br":
            return dict()

        operand_strs = list(map(str, last_inst.operands))
        if re.match(r'\s*br label', last_inst_str):
            # unconditional branch
            assert len(operand_strs) == 1
            return {str2blk[operand_strs[0]]: TRUE()}
        elif re.match(r'\s*br i1', last_inst_str):
            # conditional branch
            assert len(operand_strs) == 3
            var = str2var[operand_strs[0]]
            assert var.type.pysmt_type == BOOL
            return {str2blk[operand_strs[1]]: var.symbol,
                    str2blk[operand_strs[2]]: Not(var.symbol)}
        else:
            assert False

class Type:
    target_data = llvm.create_target_data('')
    
    def __init__(self, llvm_type: llvm.TypeRef):
        self.llvm_type = llvm_type
        self.is_pointer = self.llvm_type.is_pointer
        # get bitwidth and pysmt_type
        if llvm_type.is_pointer:
            self.bitwidth = Type.target_data.get_abi_size(llvm_type) * 8
        else:
            llvm_type_s = str(llvm_type)
            match = re.match('i\d+', llvm_type_s)
            assert match != None
            bits_str = match.group(0)[1:]
            self.bitwidth = int(bits_str)

        if self.bitwidth == 1:
            self.pysmt_type = BOOL
        else:
            self.pysmt_type = BVType(self.bitwidth)

class SymbolicStore:
    def __init__(self, fn: Function):
        self.fn = fn
        self.tab = dict()

    def alloc(self, var: Variable):
        assert not var in self.tab
        self.tab[var] = None

    def store(self, var: Variable, val: pysmt.formula):
        assert var in self.tab
        self.tab[var] = val

    def load(self, var: Variable) -> pysmt.formula:
        assert var in self.tab
        return self.tab[var]

class ExecutionEngine:
    def __init__(self, fn: Function):
        self.fn = fn
        self.symstore = SymbolicStore(fn)
        # self.path type: [(block: Block, formula: pysmt.formula)],
        # where block is component of path and formula is the symbolic expression that must be true
        # to transition from previous block to this block (for the first block, it is simply 'True')
        self.path = list()
        # TODO

    def run(self, steps):
        start_blkname = str(len(list(fn.arguments)))
        start_blk = fn.blkname_to_block(start_blkname)
        self.path.append((start_blk, TRUE)) # add first block

        # TODO

parser = argparse.ArgumentParser()
parser.add_argument('file', type=str, nargs=1)
parser.add_argument('-f', '--funcs', type=str, default='malloc,free')
args = parser.parse_args()
funcs = args.funcs.split(',')
if len(funcs) != 2:
    print('{}: --funcs: exactly two comma-separated function names are required'.
          format(sys.argv[0]), file=sys.stderr)
    exit(1)
assert len(args.file) == 1
ll_path = args.file[0]
module = Module.parse_file(ll_path)

for fn in module.function_definitions:
    for blk in fn.blocks:
        continue

    path = list()
    path.append((fn.blocks[0], []))

    store = SymbolicStore(fn)
    assignments = dict(map(lambda arg: (arg, arg.symbol), fn.arguments))
    for inst in fn.blocks[0].instructions[:-1]:
        inst.apply(path, assignments, store)

    print(path)



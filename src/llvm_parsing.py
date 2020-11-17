# type declarations
SymbolicStore = None
Block = None

from copy import copy
import enum
import math
import re # regex parsing
from typing import List, Tuple

from llvmlite import binding as llvm
#from llvmlite import ir as lc

from pysmt.shortcuts import * # are both imports here necessary?
from pysmt.typing import *


__all__ = ["Module", "Function", "Variable", "Instruction", "Block"]


'''
This file defines classes which are wrappers around functionality provided by
llvmlite, a package which allows us to work with the IR of the llvm compiler.

Module: keeps a list of global variables, i.e. functions defined in the C file.
TODO: currently doesn't handle global vairables that aren't functions.
We will iteratively verify each function definition stored in the Module

Value: A value as defined by llvmlite. Subclassed by Function, (TODO etc)

Function: Tracks arguments to a function as well as its control flow graph 

Variable: represents a variable of the program. Tracks the variable\'s name
and type and additionally stores the Symbol representing the variable in
symbolic model checking.
This class includes many functions to compute variables referred to in various
portions of the LLVM IR and additionally includes a method new_symbol that
updates the symbol corresponding to this variable, useful if for example we
are checking a loop.

Instruction: tracks operands, opcode, and, if any, the variable assigned.
Instruction.apply() applies an instruction to continue a path of symbolic
execution, tracking the formulae that must be true in order to execute this
instruction, and as a result of this instruction executing.

Block: tracks a block name (typically a number), predecessors and successors,
a list of instructions, and whether the block returns.
Block.apply() calls Instruction.apply() for each instruction successively, and
updates the formulae for conditions for each successor to be visited to include
any symbol updates by Variable.new_symbol.

Type: is a wrapper for llvm.TypeRef, useful for things like determining the bit
width of a variable.
'''


class Module:
    def __init__(self, llvm_module: llvm.ModuleRef):
        self.llvm_module = llvm_module

        # first create global variables
        str2var = dict()
        for llvm_fn in llvm_module.functions:
            str2var[str(llvm_fn)] = Variable.from_func(llvm_fn)
        assert len(list(llvm_module.global_variables)) == 0,\
            "TODO: can't handle global variables yet"
        
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

        # compute successors and populate instructions
        for blk in self.blocks:
            blk.populate(str2var, str2blk)
        
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
        
    def __repr__(self):
        return '{{.name = {}, .type = {}, .symbol = {}}}'.format(self.name, self.type, self.symbol)

    def new_symbol(self):
        self.symbol = Symbol(self.symbol.symbol_name() + '^', self.type.pysmt_type)
        return self.symbol
    
    @staticmethod
    def from_inst(llvm_inst: llvm.ValueRef):
        # name
        llvm_inst_str = str(llvm_inst)
        full_name = re.search('%\w+', llvm_inst_str).group(0)
        name = full_name[1:]
        return Variable(llvm_inst, llvm_inst.block.function.name + '_' + name)

    @staticmethod
    def from_arg(llvm_arg: llvm.ValueRef):
        # name
        llvm_arg_str = str(llvm_arg)
        name = llvm_arg_str.split()[1][1:]
        return Variable(llvm_arg, llvm_arg.function.name + '_' + name)

    # works with both declarations and definitions
    @staticmethod
    def from_func(llvm_decl: llvm.ValueRef):
        # TODO: possible name collisions with global variables
        return Variable(llvm_decl, llvm_decl.name)

class Immediate(Value):
    def __init__(self, llvm_op: llvm.ValueRef):
        Value.__init__(self, llvm_op)
        llvm_op_str = str(llvm_op)
        val_str = llvm_op_str.split()[1]
        if val_str == 'null':
            self.imm = 0
        elif val_str == 'false':
            self.imm = 0
        elif val_str == 'true':
            self.imm = 1
        elif val_str == 'inttoptr':
            self.imm = int(llvm_op_str.split()[3])
        else:
            self.imm = int(llvm_op_str.split()[1])
        self.type = Type(llvm_op.type)
        self.pysmt_formula = self._get_pysmt_formula()

    def __repr__(self) -> str:
        return '{{.imm = {}, .type = {}}}'.format(self.imm, self.type)
        
    def _get_pysmt_formula(self):
        if self.type.pysmt_type.is_bool_type():
            m = {0: FALSE, 1: TRUE}
            return m[self.imm]
        elif self.type.pysmt_type.is_bv_type():
            return (BV if self.imm >= 0 else SBV)(self.imm, self.type.pysmt_type.width)
        else:
            assert False
        
class Operand(Value):
    # TODO: enumeration of possibilities
    class Kind(enum.Enum):
        VARIABLE = enum.auto()
        IMMEDIATE = enum.auto()
        BLOCK = enum.auto()
    
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

    def __repr__(self) -> str:
        return '{{.kind = {}, .value = {}}}'.format(self.kind, self.value)

    def formula(self, assignments: dict) -> pysmt.formula:
        if self.kind == Operand.Kind.VARIABLE:
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
    def apply(self, path: List[Tuple[Block,List]], assignments: dict, store: SymbolicStore):
        if self.defined_variable != None:
            self.defined_variable.new_symbol()
        
        d = {'store': self._store,
             'icmp':  self._icmp,
             'load':  self._load,
             # applying a phi node requires knowledge of the previous block
             'phi':   lambda *args: self._phi(*args, prev_blk=path[-2][0].name),
             'alloca':self._alloca,
             'call':  self._call,
             'getelementptr': self._getelementptr,
             'sext': self._sext,
             'inttoptr': self._inttoptr,
             'bitcast': self._bitcast,
             'and': self._binop,
             'or': self._binop,
             'add': self._binop,
             }
        formula = d[self.opcode](assignments, store)
        if self.defined_variable != None:
            assert formula != None
            assignments[self.defined_variable] = formula
            #if formula != self.defined_variable.symbol:
            path[-1][1].append(EqualsOrIff(self.defined_variable.symbol, formula))
        else:
            assert formula == None

    # The below functions return the formula of the defined variable or None if
    # there is no defined variable
    
    def _bitcast(self, assignments: dict, store):
        return self.operands[0].formula(assignments)

    def _binop(self, assignments, store):
        m = {'and': BVAnd,
             'or': BVOr,
             'add': BVAdd,
             }
        return m[self.opcode](*map(lambda op: op.formula(assignments), self.operands))
        
    def _store(self, assignments: dict, store):
        dst = self.operands[1]
        val = self.operands[0]
        assert dst.value.type.is_pointer
        store.store(dst.value, val.formula(assignments))

    def _load(self, assignments: dict, store):
        src = self.operands[0]
        assert src.kind == Operand.Kind.VARIABLE
        return store.load(src.value)

    def _alloca(self, assignments: dict, store):
        store.alloc(self.defined_variable)
        return self.defined_variable.symbol

    def _icmp(self, assignments: dict, store):
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
        return formulas[cond](*atoms)

    def _phi(self, assignments: dict, store, prev_blk):
        # find branches (2nd of pairs)
        labels = re.findall('%\w+\s*\]', str(self.llvm_val))
        labels = list(map(lambda label: re.findall('\w+', label)[0], labels))
        # get blocks from labels
        assert len(labels) == len(self.operands)
        for (op, label) in zip(self.operands, labels):
            if label == prev_blk:
                return op.formula(assignments)

    def _call(self, assignments: dict, store):
        if self.defined_variable == None:
            return None # result of call is discarded
        else:
            return self.defined_variable.symbol

    def _getelementptr(self, assignments: dict, store):
        baseptr = self.operands[0]
        assert baseptr.value.type.is_pointer
        baseptr_bits = baseptr.value.type.bitwidth
        formula = baseptr.formula(assignments)

        assert len(self.operands) == 2

        index = self.operands[1]
        index_formula = index.formula(assignments)
        index_bits = index.value.type.bitwidth
        if index_bits > baseptr_bits:
            # extract lower bits from index formula
            index_formula = BVExtract(index_formula, end=(baseptr_bits - 1))
        elif index_bits < baseptr_bits:
            index_formula = BVZExt(index_formula, baseptr_bits - index_bits)

        pointee_bits = baseptr.value.type.pointee().bitwidth
        assert pointee_bits % 8 == 0
        pointee_bytes = pointee_bits / 8
        pointee_bytes_log2 = math.log(pointee_bytes, 2)
        if pointee_bytes_log2 > 0:
            index_formula = BVExtract(index_formula,
                                      end=(index_formula.bv_width - pointee_bytes_log2 - 1))
            index_formula = BVConcat(index_formula, BVZero(pointee_bytes_log2))

        formula = BVAdd(formula, index_formula)
        return formula

    def _sext(self, assignments: dict, store):
        dst_bits = self.defined_variable.type.bitwidth
        src = self.operands[0]
        src_bits = src.value.type.bitwidth
        assert dst_bits >= src_bits
        sext_formula = BVSExt(src.formula(assignments), dst_bits - src_bits)
        return sext_formula

    def _inttoptr(self, assignments: dict, store):
        dst_bits = self.defined_variable.type.bitwidth
        src_bits = self.operands[0].value.type.bitwidth
        formula = self.operands[0].formula(assignments)
        if dst_bits < src_bits:
            formula = BVExtract(formula, end=(dst_bits - 1))
        elif dst_bits > src_bits:
            formula = BVZExt(formula, dst_bits - src_bits)
        return formula
        
class Block(Value):
    def __init__(self, llvm_blk: llvm.ValueRef, str2var: dict):
        Value.__init__(self, llvm_blk)
        self.predecessors = list() # populated later
        re_name = re.match('\d+', str(llvm_blk).split('\n')[1])
        if re_name == None:
            self.name = str(len(list(llvm_blk.function.arguments)))
        else:
            self.name = re_name.group()
        
    def populate(self, str2var: dict, str2blk: dict):
        self.successors = Block._get_successors(self.llvm_val, str2var, str2blk)
        self.instructions = list(map(lambda llvm_inst: Instruction(llvm_inst, str2var, str2blk),
                                     self.llvm_val.instructions))
        # whether returns
        self.returns = self.instructions[-1].opcode in ['ret']

    def apply(self, path: List[Tuple[Block, List]], assignments: dict, store):
        for inst in self.instructions[:-1]:
            inst.apply(path, assignments, store)
        
        for successor in self.successors:
            formula = self.successors[successor]
            symbols = list(formula.get_free_variables())
            if len(symbols) != 0:
                assert len(symbols) == 1
                symbol = symbols[0]
                newf = substitute(formula, {symbol: Symbol(symbol.symbol_name() + '^',
                                                           get_type(symbol))})
                self.successors[successor] = newf
        

    @staticmethod
    def _get_successors(llvm_blk: llvm.ValueRef, str2var: dict, str2blk: dict) -> dict:
        last_inst = list(llvm_blk.instructions)[-1]
        last_inst_str = str(last_inst)
        if last_inst.opcode != 'br':
            return dict()

        operand_strs = list(map(str, last_inst.operands))
        if re.match(r'\s*br label', last_inst_str):
            # unconditional branch
            assert len(operand_strs) == 1
            return {str2blk[operand_strs[0]]: TRUE()}
        elif re.match(r'\s*br i1', last_inst_str):
            # conditional branch
            assert len(operand_strs) == 3
            if operand_strs[0] == 'i1 true':
                return {str2blk[operand_strs[2]]: TRUE(),
                        str2blk[operand_strs[1]]: FALSE(),
                        }
            elif operand_strs[0] == 'i1 false':
                return {str2blk[operand_strs[2]]: FALSE(),
                        str2blk[operand_strs[1]]: TRUE(),
                        }
                
            var = str2var[operand_strs[0]]
            assert var.type.pysmt_type == BOOL
            # NOTE: Had to swap these for some strange reason.
            return {str2blk[operand_strs[2]]: var.symbol,
                    str2blk[operand_strs[1]]: Not(var.symbol)}
        else:
            assert False

    # returns list of instructions calling a given function
    def calls(self, name: str) -> List[Instruction]:
        l = list()
        for inst in self.instructions:
            if inst.opcode == 'call':
                if inst.operands[-1].value.name == name: # fn name is the last operand
                    l.append(inst)
        return l

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

    def __repr__(self) -> str:
        return '{{.llvm_type = {}, .is_pointer = {}, .bitwidth = {}, .pysmt_type = {}}}'.format(
            self.llvm_type, self.is_pointer, self.bitwidth, self.pysmt_type)

    def value(self, val: int) -> pysmt.formula:
        if self.pysmt_type.is_bool_type():
            d = {1: TRUE(), 0: FALSE()}
            assert val in d
            return d[val]
        elif self.pysmt_type.is_bv_type():
            return BV(val, self.bitwidth)
        else:
            assert False

    def pointee(self):
        assert self.is_pointer
        return Type(self.llvm_type.element_type)


#!/usr/local/bin/python3

from llvmlite import binding as llvm
from llvmlite import ir as lc
from pysmt.shortcuts import *
from pysmt.typing import *
import sys
import re

class Variable:
    target_data = llvm.create_target_data('')
    
    def __init__(self, llvm_val: llvm.ValueRef, name: str, smt_type: PySMTType, fn):
        assert type(fn) == Function
        self.fn = fn
        self.llvm_val = llvm_val
        self.name = name
        self.smt_type = smt_type
        self.symbol = Symbol('v_' + self.name, self.smt_type)

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        return str(self)
                
    @staticmethod
    def from_inst(llvm_inst: llvm.ValueRef, fn):
        assert type(fn) == Function
        assert llvm_inst.is_instruction
        inst_str = str(llvm_inst)
        padded_assign = re.match('\s+%\w+', inst_str)
        if padded_assign == None:
            return None
        else:
            padded_assign_str = padded_assign.group(0)
            assign = padded_assign_str[padded_assign_str.find('%') + 1 : ]
            return Variable(llvm_inst, assign, Operand.get_type_from_value(llvm_inst), fn)

    # returns formula
    def get_def_constraint(self) -> pysmt.formula:
        var_dict = self.fn.variables_dict
        if self.llvm_val.is_argument:
            return TRUE()
        assert self.llvm_val.is_instruction
        inst = self.llvm_val
        inst_str = str(inst)
        inst_toks = inst_str.split()
        assert inst_toks[1] == '='
        opcode = inst.opcode
        if opcode == 'icmp':
            atoms = list(map(lambda op: Operand.get_atom_from_operand(op, self.fn), inst.operands))
            cond = inst_toks[3]
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
            return Iff(formulas[cond](*atoms), self.symbol)
        elif opcode == 'load':
            atoms = list(map(lambda op: Operand.get_atom_from_operand(op, self.fn), inst.operands))
            paths = self.fn.get_paths_to_block(self.fn.llvmblk_to_block(inst.block))
            path_constraints = map(lambda path: path.constraints, paths)
            path_stores = map(lambda path: Store.get_most_recent_store(atoms[0], path, self.fn),
                              paths)
            path_values = zip(path_constraints, path_stores)
            values = map(lambda cs: And(cs[0], Equals(self.symbol, cs[1])), path_values)
            return Or(*values)
        else:
            return None
        # TODO: other opcodes

class Store:
    @staticmethod
    def get_most_recent_store(var, path, fn):
        assert type(fn) == Function
        if type(var) == Variable:
            symbol = var.symbol
        else:
            symbol = var
        
        for blk in reversed(path.blk_list):
            for inst in reversed(list(blk.llvm_blk.instructions)):
                inst_str = str(inst)
                inst_toks = inst_str.split()
                if inst.opcode == 'store':
                    operands = list(inst.operands)
                    val_op = operands[0]
                    ptr_op = operands[1]
                    ptr_atom = Operand.get_atom_from_operand(ptr_op, fn)
                    if ptr_atom == symbol:
                        return Operand.get_atom_from_operand(val_op, fn)
        assert False # uninitialized value -- handle later
        
class Operand:
    @staticmethod
    def get_type_from_value(llvm_val: llvm.ValueRef) -> PySMTType:
        llvm_type = llvm_val.type
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
    def get_atom_from_operand(llvm_op: llvm.ValueRef, fn):
        assert llvm_op.is_operand
        assert type(fn) == Function
        var_dict = fn.variables_dict

        op_str = str(llvm_op)
        # distinguish between variables and constants
        
        full_var_re = re.search('%\w+', op_str)
        if full_var_re:
            # is variable
            full_var_str = full_var_re.group()
            return var_dict[full_var_str[1:]].symbol
        else:
            # is constant
            print('op_str:',op_str)
            op_toks = op_str.split()
            smt_type = Operand.get_type_from_value(llvm_op)
            val = int(op_toks[1])
            assert type(smt_type) == pysmt.typing._BVType
            return BV(val, smt_type.width)
            
class Block:
    def __init__(self, llvm_blk: llvm.ValueRef, variables_dict: dict):
        assert llvm_blk.is_block
        self.llvm_blk = llvm_blk
        desc = Block.get_desc(llvm_blk)
        self.name = Block.get_name(desc)
        self.pred_names = Block.get_pred_names(desc)
        self.transitions = Block.get_transitions(llvm_blk, variables_dict)
        self.insts = list(self.llvm_blk.instructions)

    def __str__(self) -> str:
        return str(self.llvm_blk)

    def __repr__(self) -> str:
        return str(self)

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

    def get_terminator(self) -> llvm.ValueRef:
        return self.insts[-1]
            
class Path:
    def __init__(self, blk_list: list):
        self.blk_list = blk_list
        self.constraints = Path.get_constraints(blk_list)
        
    def __str__(self):
        blknames = map(lambda blk: blk.name, self.blk_list)
        blkstr = ' -> '.join(blknames)
        constraint_str = str(self.constraints)
        return '({}, {})'.format(blkstr, constraint_str)

    def __repr__(self):
        return str(self)

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
        self.variables = self._get_variables(llvm_fn)
        self.variables_dict = dict(map(lambda var: (var.name, var), self.variables))
        self.llvm_fn = llvm_fn
        self.blocks = list(map(lambda llvm_blk: Block(llvm_blk, self.variables_dict),
                               llvm_fn.blocks))
        self.blkname_to_block_dict = dict(map(lambda block: (block.name, block), self.blocks))
        self.llvmblk_to_block_dict = dict(map(lambda block: (block.llvm_blk, block), self.blocks))
        self.pred_graph = self.get_pred_graph()
        self.symbol_to_var_dict = dict(map(lambda var: (var.symbol, var), self.variables))

    def __str__(self) -> str:
        return str(self.llvm_fn)

    def __repr__(self) -> str:
        return str(self)
        
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

    def _get_variables(self, llvm_fn: llvm.ValueRef) -> list:
        variables = [] 
        for llvm_blk in llvm_fn.blocks:
            for llvm_inst in llvm_blk.instructions:
                var = Variable.from_inst(llvm_inst, self)
                if var != None:
                    variables.append(var)

        # add function arguments
        i = 0
        for arg in llvm_fn.arguments:
            variables.append(Variable(arg, str(i), Operand.get_type_from_value(arg), self))
            i += 1
        
        return variables

    def get_variable(self, name: str) -> Variable:
        return self.variables_dict[name]

    def pysmtsym_to_variable(self, pysmtsym: Symbol) -> Variable:
        return self.symbol_to_var_dict[pysmtsym]

    def pysmtsyms_to_variables(self, pysmtsyms) -> list:
        expected_types = [pysmt.formula, pysmt.fnode.FNode, list]
        assert type(pysmtsyms) in expected_types
        if type(pysmtsyms) != list:
            pysmtsyms = pysmtsyms.get_free_variables()
            
        return list(map(self.pysmtsym_to_variable, pysmtsyms))

    def define_formula_variables(self, formula: pysmt.formula) -> pysmt.formula:
        # get free variables
        undefined_vars = self.pysmtsyms_to_variables(formula)

        # fully define them
        defined_vars = set()
        def_formulas = list()
        while len(undefined_vars) > 0:
            var = undefined_vars.pop()
            def_formula = var.get_def_constraint()
            def_formulas.append(def_formula)
            defined_vars.add(var)
            free_vars = set(self.pysmtsyms_to_variables(def_formula))
            undefined_vars.extend(free_vars - defined_vars)

        return And(*def_formulas)
            
    def get_block_paths(self, hit_blocks, miss_blocks) -> list:
        full_paths = self.get_full_paths()
        if type(hit_blocks) != set:
            hit_blocks = set(hit_blocks)
        if type(miss_blocks) != set:
            miss_blocks = set(miss_blocks)
        
        def filter_pred(path: Path) -> bool:
            block_set = set(path.blk_list)
            hits = len(block_set & hit_blocks) != 0
            misses = len(block_set & miss_blocks) != 0
            return hits != misses
        
        return list(filter(filter_pred, full_paths))

    # get list of blocks that exit the function
    def get_exit_blocks(self) -> list:
        terminators = ['ret', 'unreachable']
        blocks = list()
        return list(filter(lambda block: block.get_terminator().opcode in terminators, self.blocks))

    def get_full_paths(self) -> list:
        exit_blocks = self.get_exit_blocks()
        exit_paths = list()
        for exit_block in exit_blocks:
            exit_paths.extend(self.get_paths_to_block(exit_block))
        return exit_paths
        
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
    
    # find frees without corresponding mallocs and mallocs without corresponding frees
    paths = list(filter(lambda path: malloc_blk in path, fn.get_paths_to_block(free_blk)))
    assert len(paths) > 0
    path_constraints = list(map(lambda path: path.constraints, paths))
    formula = Or(*path_constraints)
    print('formula (w/o defs):', formula)
    formula = And(fn.define_formula_variables(formula), formula)
    print('formula (w/ defs):', formula)

    print('path constraints:', path_constraints)

    free_vars = list(map(fn.pysmtsym_to_variable, formula.get_free_variables()))
    print('free variables:', free_vars);

    print(list(map(lambda var: str(var), fn.variables)))

    print('printing variable constraints')
    for var in fn.variables:
        print(var, var.get_def_constraint())
    print('done')

    print('exit paths:', fn.get_full_paths())

    malloc_blocks = map(lambda inst: fn.llvmblk_to_block(inst.block), mallocs)
    free_blocks = map(lambda inst: fn.llvmblk_to_block(inst.block), frees)
    
    bad_paths = fn.get_block_paths(malloc_blocks, free_blocks)
    bad_path_constraints = list(map(lambda path: path.constraints, bad_paths))
    formula = Or(*bad_path_constraints)
    print('formula (w/o defs):', formula)
    formula = And(fn.define_formula_variables(formula), formula)
    print('formula (w/ defs):', formula)
    
    
    with Solver() as solver:
        solver.add_assertion(formula)
        print('formula:', formula)
        res = solver.solve()
        if res:
            print('SAT')
            # print_solution(solver.get_model())
            print(solver.get_model())
        else:
            print('UNSAT')

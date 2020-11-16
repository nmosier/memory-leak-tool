#!/usr/local/bin/python3

from llvm_wrappers import *
from smt_tools import *

from pysmt.shortcuts import *
from pysmt.typing import *
import argparse
from copy import copy
import math

def flatten(container: list) -> list:
    acc = list()
    for e in container:
        if type(e) == list:
            acc.extend(flatten(e))
        else:
            acc.append(e)
    return acc

def path_get_calls(path: list[Block], *args) -> list[Instruction]:
    t = tuple(map(lambda name: flatten(list(map(lambda blk: blk.calls(name), path))), args))
    return t[0] if len(t) == 1 else t

    
class ExecutionEngine:
    def __init__(self, fn: Function, preds: list, assumptions: list, open_fn, close_fn,
                 bmc: int = 20):
        self.fn = fn
        self.preds = preds
        self.assumptions = assumptions
        self.open_fn = open_fn
        self.close_fn = close_fn
        self.bmc = bmc
        # self.path type: [(block: Block, formula: pysmt.formula)],
        # where block is component of path and formula is the symbolic expression that must be true
        # to transition from previous block to this block (for the first block, it is simply 'True')

    @staticmethod
    def _copy_path(path: list) -> list:
        return list(map(copy, path))

    @staticmethod
    def _copy_assignments(assignments: dict) -> dict:
        return copy(assignments)

    @staticmethod
    def _copy_store(store: dict) -> dict:
        return copy(store)
        
    def run_block(self, block: Block, path: list, assignments: dict, store: SymbolicStore):
        block.apply(path, assignments, store)

    def run_rec(self, block: Block, path: list, assignments: dict, store: SymbolicStore):
        path = self._copy_path(path)
        assignments = self._copy_assignments(assignments)
        store = self._copy_store(store)

        # add this block to path
        path.append((block, list()))

        # apply instructions 
        self.run_block(block, path, assignments, store)
        
        # Is this point reachable?
        check_res = self.check(path, assignments)

        if not check_res:
            return

        # BMC exceeded?
        if len(path) >= self.bmc:
            return
        
        # recurse on branches
        for suc_blk in block.successors:
            suc_pred = block.successors[suc_blk]
            path[-1][1].append(suc_pred)
            self.run_rec(suc_blk, path, assignments, store)
            del path[-1][1][-1]

    # returns whether to continue
    def check(self, path: list, assignments: dict) -> bool: 
        
        constraints = list()
        for pair in path:
            for constraint in pair[1]:
                constraints.append(constraint)
        formula = And(*constraints)

        print('=================')
        print('path:', list(map(lambda pair: pair[0].name, path)))
        print('formula:', serialize(formula))

        retv = True
        
        with Solver() as solver:
            solver.add_assertion(formula)
            res_reachability = solver.solve()

            if not res_reachability:
                print('UNREACHABLE')
                retv = False
            else:
                model = solver.get_model()
                values = model.get_values(map(lambda arg: arg.symbol, self.fn.arguments))
                print('REACHABLE:', values)
            
                solver.push()

                path_blks = list(map(lambda p: p[0], path))

                # add assumptions
                for assumption in self.assumptions:
                    solver.add_assertion(assumption(path_blks, assignments, None))

                correctness_msgs = list(map(lambda pred: pred.msg, self.preds))
                correctness_formulas = list(map(
                    lambda pred: pred.pred(path_blks, assignments, pred.state), self.preds))
                retv = self.check_correctness_formulas(solver,
                                                       zip(correctness_formulas, correctness_msgs))

                solver.pop()

        print('=================')
        
        # return not is_sat
        return retv

    def check_correctness_formulas(self, solver, formulas) -> bool:
        retv = True
        for (formula, msg) in formulas:
            solver.push()
            solver.add_assertion(formula)
            if solver.solve():
                model = solver.get_model()
                values = model.get_values(map(lambda arg: arg.symbol, self.fn.arguments))
                print('INCORRECT: {}: {}'.format(msg, values))
                print('FORMULA: {}'.format(formula))
                print('MODEL:\n{}'.format(model))
                retv = False
            solver.pop()
            if not retv:
                break
        return retv
        
    def run(self):
        start_blk = self.fn.blocks[0]
        assignments = dict(map(lambda arg: (arg, arg.symbol), fn.arguments))
        self.run_rec(start_blk, list(), assignments, SymbolicStore(self.fn))

class FunctionModel:
    # rv_valid: callback that returns pysmt.formula determining wether r.v. of function call valid
    def __init__(self, name: str, valid, invalid):
        self.name = name
        self.valid = valid
        self.invalid = invalid

class CorrectnessPredicate:
    def __init__(self, pred, init_state, msg):
        self.pred = pred
        self.state = init_state
        self.msg = msg
        
class TwoCallVerifier:
    def __init__(self, open_fn, close_fn):
        preds = [CorrectnessPredicate(self.double_close_pred, None, 'double close'),
                 CorrectnessPredicate(self.opens_have_close_pred, list(), 'open w/o close'),
                 CorrectnessPredicate(self.closes_have_open_pred, None, 'close w/o open'),
                 CorrectnessPredicate(self.closes_valid_arg_pred, None,
                                      'invalid argument to close'),
        ]
        assumptions = [self.opens_distinct_assumption] # , self.opens_valid_rv_assumption]
        self.open_fn = open_fn
        self.close_fn = close_fn
        self.eng = ExecutionEngine(fn, preds, assumptions, open_fn, close_fn)

    def run(self):
        self.eng.run()

    def get_calls(self, path: list[Block]) -> tuple:
        return path_get_calls(path, self.open_fn.name, self.close_fn.name)

    def double_close_pred(self, path: list[Block], assignments: dict, state) -> pysmt.formula:
        (opens, closes) = self.get_calls(path)
        return Not(AllDifferent(*map(lambda c: c.operands[0].formula(assignments), closes)))

    def opens_have_close_pred(self, path: list[Block], assignments: dict, state) -> pysmt.formula:
        if not path[-1].returns:
            return FALSE()
        
        (opens, closes) = self.get_calls(path)

        # if valid(open), then find close
        def open_has_close(open: Instruction) -> pysmt.formula:
            return Or(*map(lambda close: EqualsOrIff(open.defined_variable.symbol,
                                                close.operands[0].formula(assignments)), closes))

        opens_have_close = map(open_has_close, opens)
        opens_valid = map(lambda open: self.open_fn.valid(open, assignments), opens)
        valid_opens_have_close = map(lambda t: Implies(*t), zip(opens_valid, opens_have_close))
        return Not(And(*valid_opens_have_close))

    def closes_have_open_pred(self, path, assignments, state):
        (opens, closes) = self.get_calls(path)
        print('opens {} closes {}'.format(len(opens), len(closes)))
        def close_has_open(close: Instruction) -> pysmt.formula:
            return Or(*map(lambda open: EqualsOrIff(open.defined_variable.symbol,
                                               close.operands[0].formula(assignments)), opens))
        return Not(And(*map(close_has_open, closes)))

    def closes_valid_arg_pred(self, path, assignments, state):
        (opens, closes) = self.get_calls(path)
        return Not(And(*map(lambda i: self.close_fn.valid(i, assignments), closes)))

    def opens_valid_rv_assumption(self, path, assignments, state):
        (opens, closes) = self.get_calls(path)
        return And(*map(lambda i: self.open_fn.valid(i, assignments), opens))
        
    def opens_distinct_assumption(self, path, assignments, state):
        (opens, closes) = self.get_calls(path)
        return AllDifferent(*map(lambda open: open.defined_variable.symbol, opens))

    
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

    def malloc_invalid_rv(inst, assignments) -> pysmt.formula:
        return Equals(inst.defined_variable.symbol, BVZero(inst.defined_variable.type.bitwidth))
    
    def malloc_valid_rv(inst, assignments) -> pysmt.formula:
        return NotEquals(inst.defined_variable.symbol, BVZero(inst.defined_variable.type.bitwidth))

    def open_valid_rv(inst, assignments) -> pysmt.formula:
        return BVSGE(inst.defined_variable.symbol, BVZero(inst.defined_variable.type.bitwidth))

    def open_invalid_rv(inst, assignments) -> pysmt.formula:
        return BVSLT(inst.defined_variable.symbol, BVZero(inst.defined_variable.type.bitwidth))

    def close_valid_arg(inst, assignments) -> pysmt.formula:
        f = inst.operands[0].formula(assignments)
        return BVSGE(f, BVZero(f.bv_width()))

    def close_invalid_arg(inst, assignments) -> pysmt.formula:
        f = inst.operands[0].formula(assignments)
        return BVSLT(f, BVZero(f.bv_width()))

    def mmap_valid_rv(inst, assignments) -> pysmt.formula:
        return NotEquals(inst.defined_variable.symbol, SBV(-1, inst.defined_variable.type.bitwidth))

    def mmap_invalid_rv(inst, assignments) -> pysmt.formula:
        return Equals(inst.defined_variable.symbol, SBV(-1, inst.defined_variable.type.bitwidth))

    def munmap_valid_arg(inst, assignments):
        f = inst.operands[0].formula(assignments)
        return NotEquals(f, SBV(-1, f.bv_width()))

    def munmap_invalid_arg(inst, assignments):
        f = inst.operands[0].formula(assignments)
        return Equals(f, SBV(-1, f.bv_width()))
    
    malloc_fn = FunctionModel('malloc', malloc_valid_rv, malloc_invalid_rv)
    free_fn = FunctionModel('free', lambda a, b: TRUE(), lambda a, b: FALSE())

    open_fn = FunctionModel('\x01_open', open_valid_rv, open_invalid_rv)
    close_fn = FunctionModel('\x01_close', close_valid_arg, close_invalid_arg)

    mmap_fn = FunctionModel('\x01_mmap', mmap_valid_rv, mmap_invalid_rv)
    munmap_fn = FunctionModel('\x01_munmap', munmap_valid_arg, munmap_invalid_arg)

    print('====== MALLOC/FREE =======')
    verifier = TwoCallVerifier(malloc_fn, free_fn)
    verifier.run()
    
    print('====== OPEN/CLOSE =======')
    verifier = TwoCallVerifier(open_fn, close_fn)
    verifier.run()

    print('====== MMAP/MUNMAP =======')
    verifier = TwoCallVerifier(mmap_fn, munmap_fn)
    verifier.run()
    

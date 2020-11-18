#!/usr/local/bin/python3

from llvm_util import *
from correctness_statements import *

import argparse
from copy import copy
from typing import List

from pysmt.shortcuts import *
from pysmt.typing import *

    
class ExecutionEngine:
    def __init__(self, fn: Function, preds: list, assumptions: list, open_fn, close_fn,
                 bmc: int = 20):
        self.fn = fn
        self.predicates = preds
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

    def run(self):
        start_blk = self.fn.blocks[0]
        assignments = dict(map(lambda arg: (arg, arg.symbol), fn.arguments))
        self.run_rec(start_blk, list(), assignments, SymbolicStore(self.fn))    
        
    def run_block(self, block: Block, path: list, assignments: dict, store: SymbolicStore):
        block.apply(path, assignments, store)

    def run_rec(self, block: Block, path: list, assignments: dict, store: SymbolicStore):
        """ Recursively run model checking, depth-first """
        path = self._copy_path(path)
        assignments = self._copy_assignments(assignments)
        store = self._copy_store(store)

        # add this block to path and run its code symbolically
        path.append((block, list()))
        self.run_block(block, path, assignments, store)
        
        # Is this path reachable? And are all our predicates still true?
        if verbose: print('=================')
        check_res = self.check(path, assignments)
        if verbose: print('=================')

        if not check_res:
            return

        # BMC exceeded?
        if len(path) >= self.bmc:
            return
        
        # recurse on branches
        successors = block.compute_successors([blk for blk, _ in path])
        for suc_blk in successors:
            suc_pred = successors[suc_blk]
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

        if verbose:
            print('path:', list(map(lambda pair: pair[0].name, path)))
            print('formula:', serialize(formula))

        # model checking
        with Solver() as solver:
            solver.add_assertion(formula)
            res_reachability = solver.solve()

            if not res_reachability:
                if verbose: print('UNREACHABLE')
                return False

            model = solver.get_model()
            values = model.get_values(map(lambda arg: arg.symbol, self.fn.arguments))
            if verbose:
                print('REACHABLE:', values)
            
            solver.push()

            path_blks = list(map(lambda p: p[0], path))

            # add assumptions
            for assumption in self.assumptions:
                solver.add_assertion(assumption(path_blks, assignments))

            # check if any predicate can fail
            for pred in self.predicates:
                solver.push()
                formula = pred(path_blks, assignments)
                solver.add_assertion(Not(formula))
                if solver.solve(): # if the predicate fails
                    model = solver.get_model()
                    values = model.get_values(map(lambda arg: arg.symbol, self.fn.arguments))
                    print('INCORRECT: {}: {}'.format(pred.msg, values))
                    print('FALSE FORMULA: {}'.format(formula))
                    print('MODEL:\n{}'.format(model))
                    print('ASSIGNMENTS: {}'.format({k.symbol:assignments[k] for k in assignments}))
                    return False
                solver.pop()

            solver.pop() # TODO is this pair necessary?
            return True

        

parser = argparse.ArgumentParser()
parser.add_argument('file', type=str, nargs=1) 
parser.add_argument('-v', '--verbose', action='store_true', dest='verbose')
args = parser.parse_args()
assert len(args.file) == 1
ll_path = args.file[0]
module = Module.parse_file(ll_path)
verbose = args.verbose

def two_call_verify(fn_to_verify, open_fn, close_fn):
    """Verify that the two functions open_fn and close_fn (given as instances
       of FunctionModel and defined in correctness_statement.py) will always be
       called in pairs"""
    preds = make_predicates(open_fn, close_fn)
    assumptions = make_assumptions(open_fn, close_fn)
    engine = ExecutionEngine(fn_to_verify, preds, assumptions, open_fn, close_fn)
    engine.run()

for fn in module.function_definitions:
    print('====== MALLOC/FREE =======')
    two_call_verify(fn, malloc_fn, free_fn)
    
    print('====== OPEN/CLOSE =======')
    two_call_verify(fn, open_fn, close_fn)

    print('====== MMAP/MUNMAP =======')
    two_call_verify(fn, mmap_fn, munmap_fn)
    

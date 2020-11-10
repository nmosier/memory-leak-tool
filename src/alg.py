from pysmt.shortcuts import *
from pysmt.typing import *
from llvmlite import binding as llvm
from llvmlite import ir as lc

class SymbolicStore:
    def __init__(self, fn: Function):
        self.fn = fn
        self.tab = dict()

    def alloc(var: Variable):
        assert not var in self.tab
        self.tab[var] = None

    def store(var: Variable, val: pysmt.formula):
        assert var in self.tab
        self.tab[var] = val

    def load(var: Variable) -> pysmt.formula:
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

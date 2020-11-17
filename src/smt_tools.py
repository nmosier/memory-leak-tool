# type declaration
Function = Variable = None

from pysmt.shortcuts import *
from pysmt.typing import *

from copy import copy

__all__ = ["SymbolicStore"]

class SymbolicStore:
    def __init__(self, fn: Function):
        self.fn = fn
        self.tab = dict()

    def __copy__(self):
        store = SymbolicStore(self.fn)
        store.tab = copy(self.tab)
        return store

    def alloc(self, var: Variable):
        assert not var in self.tab
        self.tab[var] = None

    def store(self, var: Variable, val: pysmt.formula):
        assert var in self.tab
        self.tab[var] = val

    def load(self, var: Variable) -> pysmt.formula:
        assert var in self.tab
        return self.tab[var]



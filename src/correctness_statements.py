from typing import Any, Callable, Dict, List

from pysmt.shortcuts import *

# type declarations
Block = Any
Instruction = Any
pysmt_formula = Any

'''
Tools to build correctness statements given two resource allocation/
deallocation functions (``open''/``close'') which must be called in pairs.

FunctionModel: Contains the formula which determines whether the resource
has been successfully (de)allocated. This is important because we want to
verify that every successful allocation has a corresponding deallocation,
but that we do not attempt deallocations after unsuccessful allocations.

We instantiate FunctionModel for malloc/free, open/close and mmap/munmap.

Statement: effectively a function that takes in an execution path and a
set of symbolic assignments and returns a symbolic formula capturing a
desired correctness property. We split these into two categories:
- Assumptions: statements that are true about any valid execution path
- Correctness Predicates: statements that we will attempt to verify
Predicates additionally have an error message that will be printed if
the model checker successfully falsifies the predicate.

'''

__all__ = [
    'malloc_fn', 'free_fn', 'open_fn', 'close_fn', 'mmap_fn', 'munmap_fn',
    'make_predicates', 'make_assumptions']

# ===================================
# Symbolic statements about functions
# ===================================

# Includes FunctionModel class and implementations of it for three
# pairs of resource allocation/deallocation functions, which are
# malloc/free, open/close, and mmap/munmap

class FunctionModel:
    """ name is the name of the function
        succeeded is a function (inst: Instruction, assignments: dict) -> pysmt.formula
            which returns a symbolic formula in terms of the assigned variable of inst,
            which formula is equivalent to the function succeeding / not returning an error.
        We will verify that the only calls to an open function (e.g. malloc()) that
            have a corresponding call to a close function (e.g. free()) are those
            that succeed"""
    def __init__(self, name: str, succeeded: Callable[[Instruction, Dict], pysmt_formula]):
        self.name = name
        self.succeeded = succeeded

def malloc_succeeded(inst, assignments) -> pysmt.formula:
    return NotEquals(inst.defined_variable.symbol, BVZero(inst.defined_variable.type.bitwidth))

def open_succeeded(inst, assignments) -> pysmt.formula:
    return BVSGE(inst.defined_variable.symbol, BVZero(inst.defined_variable.type.bitwidth))
def close_valid_arg(inst, assignments) -> pysmt.formula:
    f = inst.operands[0].formula(assignments)
    return BVSGE(f, BVZero(f.bv_width()))

def mmap_succeeded(inst, assignments) -> pysmt.formula:
    return NotEquals(inst.defined_variable.symbol, SBV(-1, inst.defined_variable.type.bitwidth))
def munmap_valid_arg(inst, assignments):
    f = inst.operands[0].formula(assignments)
    return NotEquals(f, SBV(-1, f.bv_width()))

malloc_fn = FunctionModel('malloc', malloc_succeeded)
free_fn = FunctionModel('free', lambda a, b: TRUE())

open_fn = FunctionModel('\x01_open', open_succeeded)
close_fn = FunctionModel('\x01_close', close_valid_arg)

mmap_fn = FunctionModel('\x01_mmap', mmap_succeeded)
munmap_fn = FunctionModel('\x01_munmap', munmap_valid_arg)


# =========================================================
# Statements determining valid and correct execution traces
# =========================================================

# Includes Statement class, some predicates and assumptions
# extending Statement, and functions make_predicates() and
# make_assumptions() to give the list of predicates/
# assumptions corresponding to a given pair of open/close
# functions (like malloc/free)

class Statement:
    def __init__(self, open_fn: FunctionModel, close_fn: FunctionModel, msg):
        """ open_fn / close_fn are a pair like malloc/free
            if this is a predicate, then msg should be an error message, to be
            displayed when the predicate does not hold true. Else, msg can be
            None. """
        self.open_fn = open_fn
        self.close_fn = close_fn
        if msg != None: self.msg = msg
    
    def __call__(self, path:List[Block], assignments: Dict) -> pysmt.formula:
        raise NotImplementedError()

    @staticmethod
    def _get_calls_fn(path: List[Block], fn_name):
        return sum((blk.calls(fn_name) for blk in path), [])

    def get_calls(self, path:List[Block]):
        return (self._get_calls_fn(path,self.open_fn.name),
                self._get_calls_fn(path,self.close_fn.name))

class DoubleClosePred(Statement):
    def __call__(self, path, assignments):
        (opens, closes) = self.get_calls(path)
        return AllDifferent(*map(lambda c: c.operands[0].formula(assignments), closes))

class OpensHaveClosePred(Statement):
    def __call__(self, path, assignments):
        if not path[-1].returns:
            return TRUE()
        (opens, closes) = self.get_calls(path)

        # if open succeeded, then find close
        def open_has_close(open: Instruction) -> pysmt.formula:
            return Or(*map(lambda close: EqualsOrIff(open.defined_variable.symbol,
                                                close.operands[0].formula(assignments)), closes))

        opens_have_close = map(open_has_close, opens)
        opens_succeeded = map(lambda open: self.open_fn.succeeded(open, assignments), opens)
        valid_opens_have_close = map(lambda t: Implies(*t), zip(opens_succeeded, opens_have_close))
        return And(*valid_opens_have_close)

class ClosesHaveOpenPred(Statement):
    def __call__(self, path, assignments):
        (opens, closes) = self.get_calls(path)
        def close_has_open(close: Instruction) -> pysmt.formula:
            return Or(*map(lambda open: EqualsOrIff(open.defined_variable.symbol,
                                               close.operands[0].formula(assignments)), opens))
        return And(*map(close_has_open, closes))

class ClosesValidArgPred(Statement):
    def __call__(self, path, assignments):
        (opens, closes) = self.get_calls(path)
        return And(*map(lambda i: self.close_fn.succeeded(i, assignments), closes))

class OpensSuccessfulAss(Statement):
    def __call__(self, path, assignments):
        (opens, closes) = self.get_calls(path)
        return And(*map(lambda i: self.open_fn.succeeded(i, assignments), opens))

class OpensDistinctAss(Statement):
    def __call__(self, path, assignments):
        (opens, closes) = self.get_calls(path)
        return AllDifferent(*map(lambda open: open.defined_variable.symbol, opens))

def make_predicates(open_fn, close_fn):
    preds = [
            (DoubleClosePred, 'double {c}'),
            (OpensHaveClosePred, '{o} w/o {c}'),
            (ClosesHaveOpenPred, '{c} w/o {o}'),
            (ClosesValidArgPred, 'invalid argument to {c}')
    ]
    return [
        pred(open_fn, close_fn, msg.format(o=open_fn.name, c=close_fn.name))
        for pred, msg in preds ]

def make_assumptions(open_fn, close_fn):
    assumptions = [OpensDistinctAss]#,OpensSuccessfulAss]
    return [ass(open_fn, close_fn, None) for ass in assumptions]

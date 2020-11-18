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
    'MALLOC', 'FREE', 'OPEN', 'CLOSE', 'MMAP', 'MUNMAP',
    'TwoCallTracker']

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

MALLOC = FunctionModel('malloc', malloc_succeeded)
FREE = FunctionModel('free', lambda a, b: TRUE())

OPEN = FunctionModel('\x01_open', open_succeeded)
CLOSE = FunctionModel('\x01_close', close_valid_arg)

MMAP = FunctionModel('\x01_mmap', mmap_succeeded)
MUNMAP = FunctionModel('\x01_munmap', munmap_valid_arg)


# =========================================================
# Statements determining valid and correct execution traces
# =========================================================

class TwoCallTracker:
    """tracks calls to a pair of functions like malloc/free during
    symbolic depth-first search
    Defines assumptions, which we assume to be true, and predicates,
    which we verify to be true given the assumptions"""
    
    def __init__(self, open_fn: FunctionModel, close_fn: FunctionModel):
        self.open_fn = open_fn
        self.close_fn = close_fn

        # state tracking information
        self.open_calls = []
        self.close_calls = []
        self.returns = False

    class OpenCall:
        def __init__(self, resource_ptr, success_formula):
            self.ptr = resource_ptr
            self.succeeded = success_formula
    class CloseCall:
        def __init__(self, resource_ptr, valid_formula):
            self.ptr = resource_ptr
            self.valid = valid_formula
        
    def push(self, block: Block, assignments):
        opens = block.calls_to(self.open_fn.name)
        self.open_calls.append([
            OpenCall(inst.defined_variable.symbol,
                     self.open_fn.succeeded(inst, assignments))
            for inst in opens
        ])
        closes = block.calls_to(self.close_fn.name)
        self.close_calls.append([
            CloseCall(inst.operands[0].formula(assignments),
                      self.close_fn.succeeded(inst, assignments))
            for inst in closes
        ])
        self.returns = block.returns

    def pop(self):
        self.open_calls.pop()
        self.close_calls.pop()
        self.returns = False

    def make_formulae(self):
        # flatten lists of open and close calls
        opens = sum(self.open_calls, [])
        closes = sum(self.close_calls, [])

        # make assumptions
        ass_specs = [
            #self._opens_successful_ass
            self._opens_distinct_ass
        ]
        assumptions = [ass(opens, closes) for ass in ass_specs]

        # make predicates
        pred_specs = [
            (self._double_close_pred, 'double {c}'),
            #(self._opens_have_close_pred, '{o} w/o {c}'),
            (self._closes_have_open_pred, '{c} w/o {o}'),
            (self._closes_valid_arg_pred, 'invalid argument to {c}')
        ]
        if self.returns: pred_specs.append((self._opens_have_close_pred, '{o} w/o {c}'))
        predicates = [
            (pred(opens, closes),
             msg.format(o=self.open_fn.name, c=self.close_fn.name))
            for pred, msg in pred_specs
        ]

        return (assumptions, predicates)

    @staticmethod
    def _double_close_pred(opens: List[OpenCall], closes: List[CloseCall]):
        return AllDifferent(close.ptr for close in closes)

    #@staticmethod # not static because of assertion only
    def _opens_have_close_pred(self, opens: List[OpenCall], closes: List[CloseCall]):
        assert self.returns, "should not check that opens have closes until return"
        def has_close(open: OpenCall) -> pysmt.formula:
            return Or(EqualsOrIff(open.ptr, close.ptr) for close in closes)
        return And(Implies(open.succeeded, has_close(open)) for open in opens)

    @staticmethod
    def _closes_have_open_pred(opens: List[OpenCall], closes: List[CloseCall]):
        def has_open(close: CloseCall) -> pysmt.formula:
            return Or(EqualsOrIff(close.ptr, open.ptr) for open in opens)
        return And(has_open(close) for close in closes)

    @staticmethod
    def _closes_valid_arg_pred(opens: List[OpenCall], closes: List[CloseCall]):
        return And(close.valid for close in closes)
    
    @staticmethod
    def _opens_successful_ass(opens: List[OpenCall], closes: List[CloseCall]):
        # not a good assumption to make in general
        return And(open.succeeded for open in opens)

    @staticmethod
    def _opens_distinct_ass(opens: List[OpenCall], closes: List[CloseCall]):
        # although this can be false, it is true in the general case, so it will
        # not compromise the validity of verification
        return AllDifferent(open.ptr for open in opens)

# for type annotations only
OpenCall = TwoCallTracker.OpenCall
CloseCall = TwoCallTracker.CloseCall

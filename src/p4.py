from pysmt.shortcuts import *
from pysmt.typing import *

# Create new symbol at time k
def symbol_at_time(sym, k):
    return Symbol('{}@{}'.format(sym.symbol_name(), k), sym.symbol_type())

### Bounded Model Checking (BMC) loop
def bmc(max_bound):
    # Bit-vector types and some constants
    BV32 = BVType(32) # create a type of Bit-Vector of size 32
    zero = BVZero(32) # create a constant value 0
    s1_init = BV(30, 32)
    s2_init = BV(20, 32)
    cons35 = BV(35, 32)

    # Inputs
    a1 = Symbol("a1", BV32) # create variable a1 with type Bit-Vector of size 32
    a2 = Symbol("a2", BV32)

    # States
    s1 = Symbol("s1", BV32)
    s2 = Symbol("s2", BV32)

    # Next state functions
    next_s1 = BVAdd(s1, a1)
    next_s2 = BVAdd(s2, a2)

    # Property
    prop = NotEquals(BVAdd(next_s1, next_s2), cons35)

    # Set initial states/input/property
    s1_at_k = s1_init
    s2_at_k = s2_init
    a1_at_k = a1
    a2_at_k = a2
    s1_at_k_next = next_s1
    s2_at_k_next = next_s2
    prop_at_k = prop

    with Solver() as solver:
        for k in range(max_bound):
            # Initialize states
            if k > 0:
                # Unroll for time k
                substs = {s1: s1_at_k,
                          s2: s2_at_k,
                          a1: a1_at_k,
                          a2: a2_at_k,
                          next_s1: s1_at_k_next,
                          next_s2: s2_at_k_next
                }
                s1_at_k_next = substitute(next_s1, substs)
                s2_at_k_next = substitute(next_s2, substs)
                prop_at_k = substitute(prop, substs)

                s1_at_k = symbol_at_time(s1, k)
                s2_at_k = symbol_at_time(s2, k)
                a1_at_k = symbol_at_time(a1, k)
                a2_at_k = symbol_at_time(a2, k)

            solver.add_assertion(Equals(s1_at_k, s1_at_k_next))
            solver.add_assertion(Equals(s2_at_k, s2_at_k_next))
            solver.add_assertion(Equals(BVAdd(a1_at_k, a2_at_k), zero))

            solver.push()

            # Check if property is violated
            solver.add_assertion(Equals(BVAdd(s1_at_k, s2_at_k), cons35));

            res = solver.solve()
            if res:
                print('Property violated @ {}'.format(k))
                print(solver.get_values([s1, s2, a1, a2]))
                break
            else:
                print('Property not violated @ {}'.format(k))

            solver.pop()

            solver.add_assertion(NotEquals(BVAdd(s1_at_k, s2_at_k), cons35))

if __name__ == '__main__':
    bmc(10)

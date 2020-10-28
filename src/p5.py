from pysmt.shortcuts import *
from pysmt.typing import *

import sys

if len(sys.argv) != 2:
    print('Usage: {} <N>'.format(sys.argv[0]))
    exit(1)

N = int(sys.argv[1])

zero = Int(0)
cons_N = Int(N)

queens = []
queens_up = []
queens_down = []

def print_solution(model):
    model = dict(map(lambda kv: (int(kv[0].symbol_name()[1:]), kv[1].constant_value()), model))
    for row in range(0, N):
        print('|', end='')
        for col in range(0, N):
            if model[col] == row:
                print('X', end='')
            else:
                print(' ', end='')
            print('|', end='')
        print('')

for i in range(N):
    queen = Symbol('q{}'.format(i), INT)
    cons = Int(i)
    queens.append(queen)
    queens_up.append(Plus(queen, cons))
    queens_down.append(Minus(queen, cons))

with Solver() as solver:
    solver.add_assertion(AllDifferent(*queens))
    solver.add_assertion(AllDifferent(*queens_up))
    solver.add_assertion(AllDifferent(*queens_down))
    for queen in queens:
        solver.add_assertion(GE(queen, zero))
        solver.add_assertion(LT(queen, cons_N))

    res = solver.solve()
    if res:
        print('SAT')
        print_solution(solver.get_model())
    else:
        print('UNSAT')


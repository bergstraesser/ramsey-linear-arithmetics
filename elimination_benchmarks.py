from z3 import *
from ramsey import *
import time


def half_int(dim: int, bound: int):
    x = IntVector('x',dim)
    y = IntVector('y',dim)
    f = And([And(2*y[i] <= x[i],x[i] >= bound) for i in range(dim)])
    output(f,x,y,[])


def half_real(dim: int, bound: float):
    x = RealVector('x',dim)
    y = RealVector('y',dim)
    f = And([And(2*y[i] <= x[i],x[i] >= bound) for i in range(dim)])
    output(f,x,y,[])


def equal_exists_int(dim: int):
    x = IntVector('x', dim)
    y = IntVector('y', dim)
    z = IntVector('z', dim)
    f = And([And(x[i] < y[i], x[i] == z[i]) for i in range(dim)])
    output(f, x, y, z)


def equal_exists_real(dim: int):
    x = RealVector('x', dim)
    y = RealVector('y', dim)
    z = RealVector('z', dim)
    f = And([And(x[i] < y[i], x[i] == z[i]) for i in range(dim)])
    output(f, x, y, z)


def equal_free_int(dim: int):
    x = IntVector('x', dim)
    y = IntVector('y', dim)
    z = IntVector('z', dim)
    f = And([And(x[i] < y[i], x[i] == z[i]) for i in range(dim)])
    output(f, x, y, [])


def equal_free_real(dim: int):
    x = RealVector('x', dim)
    y = RealVector('y', dim)
    z = RealVector('z', dim)
    f = And([And(x[i] < y[i], x[i] == z[i]) for i in range(dim)])
    output(f, x, y, [])


def dickson_int(dim: int):
    x = IntVector('x', dim)
    y = IntVector('y', dim)
    f = And([x[i] >= 0 for i in range(dim)])
    g = And(Or([y[i] < x[i] for i in range(dim)]),And([y[i] <= x[i] for i in range(dim)]))
    g = Or(g,And(Or([y[i] < x[i] for i in range(dim)]),Or([x[i] < y[i] for i in range(dim)])))
    f = And(f,g)
    output(f, x, y, [])


def dickson_real(dim: int):
    x = RealVector('x', dim)
    y = RealVector('y', dim)
    f = And([x[i] >= 0 for i in range(dim)])
    g = And(Or([y[i] < x[i] for i in range(dim)]),And([y[i] <= x[i] for i in range(dim)]))
    g = Or(g,And(Or([y[i] < x[i] for i in range(dim)]),Or([x[i] < y[i] for i in range(dim)])))
    f = And(f,g)
    output(f, x, y, [])


def program(dim: int):
    x1_r = RealVector('x1_r', dim)
    x1_i = IntVector('x1_i', dim)
    x2 = IntVector('x2', dim)
    y1_r = RealVector('y1_r', dim)
    y1_i = IntVector('y1_i', dim)
    y2 = IntVector('y2', dim)
    f1 = And([And(x1_r[i] >= 0, x1_r[i] < 1, y1_r[i] >= 0, y1_r[i] < 1) for i in range(dim)])
    f2 = And([Or(x1_i[i] > 0,And(x1_i[i] == 0, x1_r[i] > 0)) for i in range(dim)])
    f3 = And([x2[i] > 0 for i in range(dim)])
    g = []
    for i in range(dim):
        g1 = And(2*y1_i[i] == x1_i[i], 2 * y1_r[i] >= x1_r[i] + 1)
        g2 = And(2 * y1_i[i] == x1_i[i] + 1, 2 * y1_r[i] >= x1_r[i])
        g3 = 2 * y1_i[i] >= x1_i[i] + 2
        g.append(Or(g1,g2,g3))
    f4 = And(g)
    f5 = And([y2[i] <= x2[i] - x1_i[i] for i in range(dim)])
    f = And(f1,f2,f3,f4,f5)
    output(f, x1_i+x1_r+x2, y1_i+y1_r+y2, [])


def output(f: ExprRef, vars1: list[ExprRef], vars2:list[ExprRef], exvars:list[ExprRef]):
    s = Solver()
    start_time = time.time()
    f_elim, exvars_elim = eliminate_ramsey(f, vars1, vars2, exvars)
    print("Time elimination: %s sec" % (time.time() - start_time))
    s.add(f_elim)
    print(s.check())
    print("Time total: %s sec" % (time.time() - start_time))
    print("#variables input: %s" % len(get_variables(f)))
    print("#atoms input: %s" % len(get_atoms(f)))
    print("#variables output: %s" % len(get_variables(f_elim)))
    print("#atoms output: %s" % len(get_atoms(f_elim)))
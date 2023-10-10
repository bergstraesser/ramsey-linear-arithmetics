from z3 import *
from ramsey import *
import time


# From CAV'21 but they only vary K and dim = 1
def imp_int(dim: int, k: int):
    x = IntVector('x', dim)
    y = IntVector('y', dim)
    f = And([Or(x[i] < 0, And(x[i] + y[i] >= k, y[i] >= 0)) for i in range(dim)])
    output(f)


def imp_real(dim: int, k: int):
    x = RealVector('x', dim)
    y = RealVector('y', dim)
    f = And([Or(x[i] < 0, And(x[i] + y[i] >= k, y[i] >= 0)) for i in range(dim)])
    output(f)


# From CAV'21 for dim = 2
def diagonal_int(dim: int, k: int):
    x = IntVector('x', dim)
    f = And([x[0] == x[i] for i in range(1,dim)])
    f = And(f, 0 <= x[0], x[0] <= k)
    output(f)


def diagonal_real(dim: int, k: int):
    x = RealVector('x', dim)
    f = And([x[0] == x[i] for i in range(1,dim)])
    f = And(f, 0 <= x[0], x[0] <= k)
    output(f)


# From CAV'21 for dim = 2 if restricted and k = 10 if not restricted
def cubes_int(dim: int, k: int, restrict: bool):
    x = IntVector('x', dim)
    f = Or([And([And(i <= x[j], x[j] <= i+2) for j in range(dim)]) for i in range(k)])
    if restrict:
        f = And(f, sum([x[i] for i in range(1,dim)],x[0]) <= k)
    output(f)


def cubes_real(dim: int, k: int, restrict: bool):
    x = RealVector('x', dim)
    f = Or([And([And(i <= x[j], x[j] <= i+2) for j in range(dim)]) for i in range(k)])
    if restrict:
        f = And(f, sum([x[i] for i in range(1,dim)],x[0]) <= k)
    output(f)


def mixed(dim: int, l: int, u: int):
    x = IntVector('x', dim)
    y_int = IntVector('y_int', dim)
    y_real = RealVector('y_real', dim)
    f1 = And([x[i] == y_int[i] for i in range(dim)])
    f2 = And([And(0 <= y_real[i], y_real[i] < 1) for i in range(dim)])
    f3 = And([l <= y_int[i] for i in range(dim)])
    f4 = And([Or(y_int[i] < u, And(y_int[i] == u, y_real[i] == 0)) for i in range(dim)])
    output(And(f1,f2,f3,f4))


def output(f: ExprRef):
    s = Solver()
    start_time = time.time()
    mondec, not_sim, not_sim_elim = mondec_analysis(f)
    print("Mondec: %s" % mondec)
    print("Time total: %s sec" % (time.time() - start_time))
    if not_sim is None:
        print("Trivially decomposable")
    else:
        print("#variables input: %s" % len(get_variables(not_sim)))
        print("#atoms input: %s" % len(get_atoms(not_sim)))
        print("#variables output: %s" % len(get_variables(not_sim_elim)))
        print("#atoms output: %s" % len(get_atoms(not_sim_elim)))
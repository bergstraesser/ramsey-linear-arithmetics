from z3 import *
import time


# Takes a formula and checks if it is atomic
def is_atom(f: ExprRef):
    return f.sort_kind() == Z3_BOOL_SORT and f.children()[0].sort_kind() != Z3_BOOL_SORT


# Bring interger part of formula in format where only <,>, and mod are allowed and
# real part where only <,>,= are allowed
def input_format(f: ExprRef):
    if f.decl().kind() == Z3_OP_AND:
        return And([input_format(c) for c in f.children()])
    if f.decl().kind() == Z3_OP_OR:
        return Or([input_format(c) for c in f.children()])
    if f.decl().kind() == Z3_OP_NOT:
        return Not(input_format(f.children()[0]))
    # Must be atom
    if f.children()[0].sort_kind() == Z3_INT_SORT:
        if f.decl().kind() == Z3_OP_EQ and f.children()[0].decl().kind() != Z3_OP_MOD:
            return And(f.children()[0] < f.children()[1]+1, f.children()[1] < f.children()[0]+1)
        if f.decl().kind() == Z3_OP_DISTINCT and f.children()[0].decl().kind() != Z3_OP_MOD:
            return Or(f.children()[0] < f.children()[1], f.children()[1] < f.children()[0])
        if f.decl().kind() == Z3_OP_LE:
            return f.children()[0] < f.children()[1]+1
        if f.decl().kind() == Z3_OP_GE:
            return f.children()[1] < f.children()[0]+1
        return f
    else:
        if f.decl().kind() == Z3_OP_DISTINCT:
            return Or(f.children()[0] < f.children()[1], f.children()[1] < f.children()[0])
        if f.decl().kind() == Z3_OP_LE:
            return Or(f.children()[0] < f.children()[1], f.children()[0] == f.children()[1])
        if f.decl().kind() == Z3_OP_GE:
            return Or(f.children()[1] < f.children()[0], f.children()[1] == f.children()[0])
        return f


def move_negations_inside(f: ExprRef):
    if is_atom(f):
        return f
    if f.decl().kind() == Z3_OP_AND:
        return And([move_negations_inside(c) for c in f.children()])
    if f.decl().kind() == Z3_OP_OR:
        return Or([move_negations_inside(c) for c in f.children()])
    g = f.children()[0]  # Child of Not
    if is_atom(g):  # If g is atom, we negate atom
        if g.decl().kind() == Z3_OP_LT:
            if g.children()[0].sort_kind() == Z3_INT_SORT:
                return g.children()[0] > g.children()[1]-1  # left child >= right child
            else:
                return Or(g.children()[0] > g.children()[1],g.children()[0] == g.children()[1])  # left child >= right child
        elif g.decl().kind() == Z3_OP_GT:
            if g.children()[0].sort_kind() == Z3_INT_SORT:
                return g.children()[0] < g.children()[1]+1  # left child >= right child
            else:
                return Or(g.children()[0] < g.children()[1],g.children()[0] == g.children()[1])  # left child >= right child
        elif g.decl().kind() == Z3_OP_EQ:
            if g.children()[0].sort_kind() == Z3_INT_SORT:
                return g.children()[0] != g.children()[1]  # left child not congruent to right child
            else:
                return Or(g.children()[0] < g.children()[1],g.children()[0] > g.children()[1])  # left child != right child
        elif g.decl().kind() == Z3_OP_DISTINCT:  # Must be incongruence
            return g.children()[0] == g.children()[1]  # left child is congruent to right child
    # g is formula with outermost operator Not,And,Or
    if g.decl().kind() == Z3_OP_NOT:
        return move_negations_inside(g.children()[0])
    if g.decl().kind() == Z3_OP_AND:
        return Or([move_negations_inside(Not(c)) for c in g.children()])
    if g.decl().kind() == Z3_OP_OR:
        return And([move_negations_inside(Not(c)) for c in g.children()])


def simp(f: ExprRef, vars: list[ExprRef]):
    if f.decl().kind() == Z3_OP_AND:  # For some reason f.decl() can only take two arguments
        return And([simp(c, vars) for c in f.children()])
    if f.decl().kind() == Z3_OP_OR:
        return Or([simp(c, vars) for c in f.children()])
    if f.decl().kind() == Z3_OP_LT:
        left = subterm(simplify(f.children()[0]),vars,True)
        right = subterm(simplify(f.children()[1]),vars,False)
        return simplify(f.children()[0]-left-right) < simplify(f.children()[1]-left-right)
    if f.decl().kind() == Z3_OP_GT:
        left = subterm(simplify(f.children()[0]),vars,False)
        right = subterm(simplify(f.children()[1]),vars,True)
        return simplify(f.children()[0]-left-right) > simplify(f.children()[1]-left-right)
    if f.decl().kind() == Z3_OP_EQ and f.children()[0].decl().kind() != Z3_OP_MOD:  # equality and not mod
        left = subterm(simplify(f.children()[0]), vars, True)
        right = subterm(simplify(f.children()[1]), vars, False)
        return simplify(f.children()[0] - left - right) == simplify(f.children()[1] - left - right)
    else:  # mod constraint
        lterm = f.children()[0].children()[0]  # mod is outermost operator
        rterm = f.children()[1].children()[0]
        lmod = simplify(f.children()[0].children()[1])
        rmod = simplify(f.children()[1].children()[1])
        left = subterm(simplify(lterm), vars, True)
        right = subterm(simplify(rterm), vars, False)
        return f.decl()(simplify(lterm-left-right)%lmod,simplify(rterm-left-right)%rmod)


# Assumes simplified linear term
def subterm(term: ExprRef, vars: list[ExprRef], complement: Bool):
    if term.decl().kind() != Z3_OP_ADD:  # multiple of variable or constant
        if is_const(term) and term.decl().kind() != Z3_OP_UNINTERPRETED:  # If term is a value
            if complement:
                return term
            else:
                return IntVal(0)
        v = term  # v is variable or multiple of variable
        if term.decl().kind() == Z3_OP_MUL:
            v = term.children()[1]  # In simplified terms variable always right child
        if (v in vars) is not complement:
            return term
        else:
            return IntVal(0)
    res = IntVal(0)
    for c in term.children():
        res = res + subterm(c,vars,complement)
    return simplify(res)


def get_inequalities(f: ExprRef):
    if f.decl().kind() == Z3_OP_AND or f.decl().kind() == Z3_OP_OR:
        res = []
        for c in f.children():
            res += get_inequalities(c)
        return res
    if f.decl().kind() == Z3_OP_LT or f.decl().kind() == Z3_OP_GT:
        return [f]
    return []


# Also for unequalities (and mod)
def get_equalities(f: ExprRef):
    if f.decl().kind() == Z3_OP_AND or f.decl().kind() == Z3_OP_OR:
        res = []
        for c in f.children():
            res += get_equalities(c)
        return res
    if f.decl().kind() == Z3_OP_EQ or f.decl().kind() == Z3_OP_DISTINCT:
        return [f]
    return []


def get_atoms(f: ExprRef):
    if is_atom(f):
        return [f]
    res = []
    for c in f.children():
        res += get_atoms(c)
    return res


# Express equality of two terms with <
def eq_int(f: ExprRef, g: ExprRef):
    return And(f < simplify(g+1), g < simplify(f+1))


# Express unequality of two terms with <
def not_eq(f: ExprRef, g: ExprRef):
    return Or(f < g, g < f)


# Input: Quantifier-free f with list exvars of existentially quantified variables
# and two non-empty lists of free variables vars1,vars2 of same length
# Output: Formula equivalent to Ram vars1,vars2: Exists exvars: f
def eliminate_ramsey(f: ExprRef,vars1: list[ExprRef],vars2: list[ExprRef],exvars: list[ExprRef]=[]):
    f = input_format(f)
    vs = list(set(get_variables(f)+vars1+vars2+exvars))  # not all variables must actually occur
    mixed = False
    for i in range(len(vs)-1):
        if vs[i].sort_kind() != vs[i+1].sort_kind():
            mixed = True
            break
    free = list(set(vs)-set(vars1)-set(vars2)-set(exvars))
    # rename variables
    x, y, z = [], [], []
    for i in range(len(vars1)):
        if vars1[i].sort_kind() == Z3_INT_SORT:
            x.append(Int('x__%i' % i))
        else:
            x.append(Real('x__%i' % i))
    for i in range(len(vars2)):
        if vars2[i].sort_kind() == Z3_INT_SORT:
            y.append(Int('y__%i' % i))
        else:
            y.append(Real('y__%i' % i))
    for i in range(len(free)):
        if free[i].sort_kind() == Z3_INT_SORT:
            z.append(Int('z__%i' % i))
        else:
            z.append(Real('z__%i' % i))
    v1, v2, w1, w2 = [], [], [], []
    for i in range(len(exvars)):
        if exvars[i].sort_kind() == Z3_INT_SORT:
            v1.append(Int('v1__%i' % i))
            v2.append(Int('v2__%i' % i))
            w1.append(Int('w1__%i' % i))
            w2.append(Int('w2__%i' % i))
        else:
            v1.append(Real('v1__%i' % i))
            v2.append(Real('v2__%i' % i))
            w1.append(Real('w1__%i' % i))
            w2.append(Real('w2__%i' % i))
    subs = [(vars1[i],x[i]) for i in range(len(vars1))] + [(vars2[i],y[i]) for i in range(len(vars2))]
    subs += [(free[i],z[i]) for i in range(len(free))]
    # Quantifier elimination
    subs += [(exvars[i],v1[i]+w2[i]) for i in range(len(exvars))]
    f = substitute(f, subs)
    # After QE we lose pairwise distinctness. The following ensures pairwise distinct subclique
    f = And(Or([Or(x[i]<y[i],y[i]<x[i]) for i in range(len(x))]),f)
    f = move_negations_inside(f)
    f = simp(f, x + v1 + v2)
    if mixed:
        return eliminate_ramsey_mixed(f, x + v1 + v2, y + w1 + w2)
    if vars1[0].sort_kind() == Z3_INT_SORT:
        return eliminate_ramsey_int(f,x+v1+v2,y+w1+w2)
    if vars1[0].sort_kind() == Z3_REAL_SORT:
        return eliminate_ramsey_real(f,x+v1+v2,y+w1+w2)


def eliminate_ramsey_int(f: ExprRef,vars1: list[ExprRef],vars2: list[ExprRef]):
    iqs = get_inequalities(f)
    eqs = get_equalities(f)
    atoms = iqs + eqs
    n = len(iqs)
    m = len(eqs)
    q = IntVector('q',n+m)
    restrict = And([Or(eq_int(q[i], IntVal(0)), eq_int(q[i], IntVal(1))) for i in range(n + m)])
    skeleton = substitute(f, [(atoms[i], eq_int(q[i], IntVal(1))) for i in range(n + m)])
    p = IntVector('p',2*n)
    omega = IntVector('o',2*n)
    restrict = And(restrict, And([Or(eq_int(omega[i], IntVal(0)), eq_int(omega[i], IntVal(1))) for i in range(2 * n)]))
    admissible = And([Or(And(eq_int(omega[2 * i], IntVal(0)), p[2 * i] < p[2 * i + 1]), eq_int(omega[2 * i + 1], IntVal(1))) for i in range(n)])
    b = IntVector('b',len(vars1))
    c = IntVector('c',len(vars1))
    restrict = And(restrict, Or([not_eq(c[i], IntVal(0)) for i in range(len(c))]))
    sub_var1_b = [(vars1[i],b[i]) for i in range(len(b))]
    sub_var1_c = [(vars1[i],c[i]) for i in range(len(c))]
    sub_var2_b = [(vars2[i], b[i]) for i in range(len(b))]
    sub_var2_c = [(vars2[i], c[i]) for i in range(len(c))]
    gamma = []
    for i in range(n):
        if iqs[i].decl().kind() == Z3_OP_LT:
            left = iqs[i].children()[0]
            right = iqs[i].children()[1]
        else:
            left = iqs[i].children()[1]
            right = iqs[i].children()[0]
        term_vars2 = subterm(right,vars2,False)
        g = Or(eq_int(omega[2 * i], IntVal(1)), And(substitute(left, sub_var1_b) < p[2 * i] + 1,
                                                    substitute(left,sub_var1_c) < 1))
        g = And(g,Or(eq_int(omega[2 * i + 1], IntVal(1)), And(p[2 * i + 1] - 1 < substitute(right, sub_var2_b),
                                                              -1 < substitute(term_vars2,sub_var2_c))))
        g = And(g, Or(eq_int(omega[2 * i + 1], IntVal(0)), 0 < substitute(term_vars2, sub_var2_c)))
        gamma.append(g)
    sub_var2_sum = [(vars2[i], b[i]+c[i]) for i in range(len(b))]
    for i in range(m):
        mod = eqs[i].children()[0].children()[1]
        t = eqs[i].children()[0].children()[0] + eqs[i].children()[1].children()[0]
        t1 = subterm(t,vars1,False)
        t2 = subterm(t,vars1,True)
        t3 = subterm(t2,vars2,False)
        g = eqs[i].decl()(substitute(t1,sub_var1_b)%mod,simplify(substitute(t2,sub_var2_sum))%mod)
        g = And(g,substitute(t1,sub_var1_c)%mod == 0%mod,substitute(t3,sub_var2_c)%mod == 0%mod)
        gamma.append(g)
    res = And(restrict,skeleton,admissible)
    res = And(res, And([Or(not_eq(q[i], IntVal(1)), gamma[i]) for i in range(n + m)]))
    return (res, q+p+omega+b+c)


def eliminate_ramsey_real(f: ExprRef,vars1: list[ExprRef],vars2: list[ExprRef]):
    iqs = get_inequalities(f)
    eqs = get_equalities(f)
    atoms = iqs + eqs
    n = len(iqs)
    m = len(eqs)
    q = RealVector('q', n + m)
    restrict = And([Or(q[i] == 0, q[i] == 1) for i in range(n + m)])
    skeleton = substitute(f, [(atoms[i], q[i] == 1) for i in range(n + m)])
    rho, sigma = RealVector('r',n), RealVector('s',n)
    trho, tsigma = RealVector('tr',n), RealVector('ts',n)
    restrict = And(restrict,And([Or(trho[i] == -2,trho[i] == -1,trho[i] == 0,trho[i] == 1,trho[i] == 2) for i in range(n)]))
    restrict = And(restrict,And([Or(tsigma[i] == -1,tsigma[i] == 0,tsigma[i] == 1,tsigma[i] == 2) for i in range(n)]))
    admissible = And([Or(trho[i] < 2,tsigma[i] == 2) for i in range(n)])
    g = [And(Or(Or(trho[i]==-2,trho[i]>0),Or(tsigma[i]==-1,tsigma[i]==2)),
             Or(not_eq(trho[i], RealVal(-1)), tsigma[i] > -1)) for i in range(n)]
    zterm = [subterm(iqs[i].children()[0]+iqs[i].children()[1],vars1+vars2,True) for i in range(n)]
    admissible = And(admissible,And([Or(g[i],rho[i]<sigma[i]+zterm[i]) for i in range(n)]))
    g = [And(Or(not_eq(trho[i], RealVal(0)), tsigma[i] > -1), not_eq(trho[i], RealVal(1))) for i in range(n)]
    admissible = And(admissible,And([Or(g[i],Or(rho[i]<sigma[i]+zterm[i],
                                                rho[i]==sigma[i]+zterm[i])) for i in range(n)]))
    c, d, e = RealVector('c',len(vars1)), RealVector('d',len(vars1)), RealVector('e',len(vars1))
    restrict = And(restrict, Or([not_eq(d[i], RealVal(0)) for i in range(len(vars1))]))
    xterm = [subterm(iqs[i].children()[0] + iqs[i].children()[1], vars1, False) for i in range(n)]
    yterm = [subterm(iqs[i].children()[0] + iqs[i].children()[1], vars2, False) for i in range(n)]
    r_c = [substitute(xterm[i],[(vars1[i],c[i]) for i in range(len(vars1))]) for i in range(n)]
    r_d = [substitute(xterm[i],[(vars1[i],d[i]) for i in range(len(vars1))]) for i in range(n)]
    r_e = [substitute(xterm[i],[(vars1[i],e[i]) for i in range(len(vars1))]) for i in range(n)]
    s_c = [substitute(yterm[i],[(vars2[i],c[i]) for i in range(len(vars2))]) for i in range(n)]
    s_d = [substitute(yterm[i],[(vars2[i],d[i]) for i in range(len(vars2))]) for i in range(n)]
    s_e = [substitute(yterm[i],[(vars2[i],e[i]) for i in range(len(vars2))]) for i in range(n)]
    lamb = [And(Or(Or(trho[i] == -2, trho[i] == 0, trho[i] == 2),And(r_c[i] == rho[i], r_e[i] == 0)),
                Or(Or(tsigma[i] == 0, tsigma[i] == 2),And(s_c[i] == sigma[i], s_e[i] == 0)))
            for i in range(n)]
    chi = [And(Or(not_eq(trho[i], RealVal(0)), And(r_c[i] == rho[i], r_d[i] == 0, r_e[i] == 0)),
               Or(not_eq(tsigma[i], RealVal(0)), And(s_c[i] == sigma[i], s_d[i] == 0, s_e[i] == 0)))
           for i in range(n)]
    delta = [And(Or(not_eq(trho[i], RealVal(-1)), r_d[i] < 0),
                 Or(not_eq(trho[i], RealVal(1)), r_d[i] > 0),
                 Or(tsigma[i] > -1, s_d[i] < 0),
                 Or(not_eq(tsigma[i], RealVal(1)), s_d[i] > 0)) for i in range(n)]
    mu = [And(Or(trho[i] > -2,r_e[i] < 0),
              Or(trho[i] < 2,r_e[i] > 0),
              Or(tsigma[i] < 2, s_e[i] > 0)) for i in range(n)]
    eq_xterm = [subterm(eqs[i].children()[0] + eqs[i].children()[1], vars1, False) for i in range(m)]
    eq_yterm = [subterm(eqs[i].children()[0] + eqs[i].children()[1], vars2, False) for i in range(m)]
    eq_zterm = [subterm(eqs[i].children()[0] + eqs[i].children()[1], vars1 + vars2, True) for i in range(m)]
    u_c = [substitute(eq_xterm[i], [(vars1[i], c[i]) for i in range(len(vars1))]) for i in range(m)]
    u_d = [substitute(eq_xterm[i], [(vars1[i], d[i]) for i in range(len(vars1))]) for i in range(m)]
    u_e = [substitute(eq_xterm[i], [(vars1[i], e[i]) for i in range(len(vars1))]) for i in range(m)]
    v_c = [substitute(eq_yterm[i], [(vars2[i], c[i]) for i in range(len(vars2))]) for i in range(m)]
    v_d = [substitute(eq_yterm[i], [(vars2[i], d[i]) for i in range(len(vars2))]) for i in range(m)]
    v_e = [substitute(eq_yterm[i], [(vars2[i], e[i]) for i in range(len(vars2))]) for i in range(m)]
    eps = [And(u_d[i] == 0, u_e[i] == 0, v_d[i] == 0, v_e[i] == 0,
               simplify(u_c[i]-v_c[i]) == eq_zterm[i]) for i in range(m)]
    res = And(restrict,skeleton,admissible)
    res = And(res, And([Or(q[i] == 0, And(lamb[i],chi[i],delta[i],mu[i])) for i in range(n)]))
    res = And(res, And([Or(q[n+i] == 0, eps[i]) for i in range(m)]))
    return (res, q+rho+sigma+trho+tsigma+c+d+e)


def eliminate_ramsey_mixed(f: ExprRef,vars1: list[ExprRef],vars2: list[ExprRef]):
    atoms = get_atoms(f)
    int_atoms = [a for a in atoms if a.children()[0].sort_kind() == Z3_INT_SORT]
    real_atoms = [a for a in atoms if a.children()[0].sort_kind() == Z3_REAL_SORT]
    n, m = len(int_atoms), len(real_atoms)
    int_vars1 = [v for v in vars1 if v.sort_kind() == Z3_INT_SORT]
    real_vars1 = [v for v in vars1 if v.sort_kind() == Z3_REAL_SORT]
    int_vars2 = [v for v in vars2 if v.sort_kind() == Z3_INT_SORT]
    real_vars2 = [v for v in vars2 if v.sort_kind() == Z3_REAL_SORT]
    q_int, q_real = IntVector('q_int',n), RealVector('q_real',m)
    restrict = And([Or(q == 0, q == 1) for q in q_int + q_real])
    subs = [(int_atoms[i],q_int[i]==1) for i in range(n)] + [(real_atoms[i],q_real[i]==1) for i in range(m)]
    skeleton = substitute(f, subs)
    e_int, e_real = True, True
    exvars_int, exvars_real = [], []
    l_int = Int('l_int')
    restrict = And(restrict,Or(l_int == 0, l_int == 1))
    if n > 0:
        int_part = And([Or(Or(IntVal(0) < simplify(q_int[i] - IntVal(1)), IntVal(0) < simplify(IntVal(1) - q_int[i])),
                           int_atoms[i]) for i in range(n)])
        # simplify again - not needed anymore
        # int_part = simp(int_part, int_vars1)
        e_int, exvars_int = eliminate_ramsey_int(int_part,int_vars1,int_vars2)
        loop_int_vars = [Int('l_%s' % int_vars1[i].decl().name()) for i in range(len(int_vars1))]
        loop_int = substitute(int_part, [(int_vars1[i],loop_int_vars[i]) for i in range(len(int_vars1))])
        loop_int = substitute(loop_int, [(int_vars2[i], loop_int_vars[i]) for i in range(len(int_vars1))])
        loop_int = And(l_int == 1, loop_int)
    if m > 0:
        real_part = And([Or(Or(RealVal(0) < simplify(q_real[i] - RealVal(1)), RealVal(0) < simplify(RealVal(1) - q_real[i])),
                            real_atoms[i]) for i in range(m)])
        # simplify again - not needed anymore
        # real_part = simp(real_part, real_vars1)
        e_real, exvars_real = eliminate_ramsey_real(real_part, real_vars1, real_vars2)
        loop_real_vars = [Real('l_%s' % real_vars1[i].decl().name()) for i in range(len(real_vars1))]
        loop_real = substitute(real_part, [(real_vars1[i], loop_real_vars[i]) for i in range(len(real_vars1))])
        loop_real = substitute(loop_real, [(real_vars2[i], loop_real_vars[i]) for i in range(len(real_vars1))])
        loop_real = And(l_int == 0, loop_real)
    # make existential variables distinct
    new_exvars_int = [Int('%s_int' % exvars_int[i].decl().name()) for i in range(len(exvars_int))]
    new_exvars_real = [Real('%s_real' % exvars_real[i].decl().name()) for i in range(len(exvars_real))]
    e_int = substitute(e_int, [(exvars_int[i],new_exvars_int[i]) for i in range(len(exvars_int))])
    e_real = substitute(e_real, [(exvars_real[i], new_exvars_real[i]) for i in range(len(exvars_real))])
    new_exvars = q_int + q_real + new_exvars_int + new_exvars_real + [l_int] + loop_int_vars + loop_real_vars
    res = And(restrict,skeleton,Or(e_int,loop_int),Or(e_real,loop_real))
    return (res, new_exvars)


def get_variables(f: ExprRef):
    if is_const(f):
        if f.decl().kind() == Z3_OP_UNINTERPRETED:  # variable
            return [f]
        else:  # value
            return []
    res = set()
    for c in f.children():
        res = res.union(get_variables(c))
    return list(res)


def is_mondec(f: ExprRef):
    vars = get_variables(f)
    if len(vars) < 2:
        return True
    u, v = [], []
    for i in range(len(vars)):
        if vars[i].sort_kind() == Z3_INT_SORT:
            u.append(Int('u__%i' % i))
            v.append(Int('v__%i' % i))
        else:
            u.append(Real('u__%i' % i))
            v.append(Real('v__%i' % i))
    f_u = substitute(f,[(vars[i],u[i]) for i in range(len(vars))])
    f_v = substitute(f,[(vars[i],v[i]) for i in range(len(vars))])
    for i in range(len(vars)-1):
        if vars[i].sort_kind() == Z3_INT_SORT:
            w = Int('w')
        else:
            w = Real('w')
        f_u_w, f_v_w = substitute(f_u,[(u[i],w)]), substitute(f_v,[(v[i],w)])
        g = Or(And(f_u_w,Not(f_v_w)),And(Not(f_u_w),f_v_w))
        s = Solver()
        g_elim, exvars_elim = eliminate_ramsey(g, u[:i] + u[i + 1:], v[:i] + v[i + 1:], [w])
        s.add(g_elim)
        if s.check() == sat:
            return False
    return True


def mondec_analysis(f: ExprRef):
    start_time = time.time()
    vars = get_variables(f)
    if len(vars) < 2:
        return True, None, None
    u, v = [], []
    for i in range(len(vars)):
        if vars[i].sort_kind() == Z3_INT_SORT:
            u.append(Int('u__%i' % i))
            v.append(Int('v__%i' % i))
        else:
            u.append(Real('u__%i' % i))
            v.append(Real('v__%i' % i))
    f_u = substitute(f,[(vars[i],u[i]) for i in range(len(vars))])
    f_v = substitute(f,[(vars[i],v[i]) for i in range(len(vars))])
    for i in range(len(vars)-1):
        if vars[i].sort_kind() == Z3_INT_SORT:
            w = Int('w')
        else:
            w = Real('w')
        f_u_w, f_v_w = substitute(f_u,[(u[i],w)]), substitute(f_v,[(v[i],w)])
        g = Or(And(f_u_w,Not(f_v_w)),And(Not(f_u_w),f_v_w))
        print('Iteration')
        g_elim, exvars_elim = eliminate_ramsey(g, u[:i] + u[i + 1:], v[:i] + v[i + 1:], [w])
        print("Time construction and elimination: %s sec" % (time.time() - start_time))
        if i == 0:
            not_sim = g
            not_sim_elim = g_elim
        s = Solver()
        start_time = time.time()
        s.add(g_elim)
        is_sat = s.check()
        print("Time sat check: %s sec" % (time.time() - start_time))
        if is_sat == sat:
            return False, not_sim, not_sim_elim
        start_time = time.time()
    return True, not_sim, not_sim_elim

from ramsey import *
x,y,z = Int('x'), Int('y'), Int('z')
f = And(2*x < y, x <= z)
f_elim, exvars_elim = eliminate_ramsey(f,[x],[y],[z])
s = Solver()
s.add(f_elim)
print(s.check())
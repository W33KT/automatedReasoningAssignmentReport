from z3 import *


x0 = BitVec('x0', 32)


x = x0
y = BitVecVal(1, 32)



for i in range(15):
    x= x + y
    y = 2 * y + 1


s = Solver()
s.add(x < x0 )

if s.check() == sat:
    m = s.model()
    print(m)
else:
    print("No overflow within 15 iterations.")

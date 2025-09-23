from z3 import *

x0 = Int('x0')

x = x0
y = 1

xlist = [x0]
ylist = [1]

for i in range(15):
    x = x + y
    y = 2 * y + 1
    xlist.append(x)
    ylist.append(y)


s = Solver()
s.add(xlist[14] < 1e9 , xlist[15] >= 1e9)

if s.check() == sat:
    m = s.model()
    print(m)
else:
    print("No solution")

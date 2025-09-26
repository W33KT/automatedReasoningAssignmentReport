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


opt = Optimize()
opt.add(xlist[14] < 10**9, xlist[15] >= 10**9)

h = opt.minimize(x0) 

if opt.check() == sat:
    m = opt.model()
    print("Minimal x0 =", m[x0])
else:
    print("No solution")

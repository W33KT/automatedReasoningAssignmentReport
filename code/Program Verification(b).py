from z3 import *
import time

start = time.time()

x = x0
x0 = BitVec('x0', 32)
y = BitVecVal(1, 32)


xlist = [x]
ylist = [y]

for i in range(15):
    x = x + y
    y = 2 * y + 1
    xlist.append(x)
    ylist.append(y)

s = Solver()


s.add(ULT(xlist[14], BitVecVal(10**9, 32)))   
s.add(UGE(xlist[15], BitVecVal(10**9, 32)))   


s.add(ULT(x, x0))  

if s.check() == sat:
    m = s.model()
    print("Overflow detected:", m)
else:
    print("No overflow or underflow within 15 iterations.")

end = time.time()
print("Runtime:", end - start, "seconds")

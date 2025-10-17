from z3 import *
import time

start = time.time()
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
    print("No overflow or underflow within 15 iterations.")

end = time.time()
print("Runtime:", end - start, "seconds")
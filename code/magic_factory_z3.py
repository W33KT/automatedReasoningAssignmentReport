from z3 import *
import time

# Create integer variables for each truck and pallet type
n = [Int(f"n_{i}") for i in range(8)]  # nuzzles
p = [Int(f"p_{i}") for i in range(8)]  # prittles
s = [Int(f"s_{i}") for i in range(8)]  # skipples
c = [Int(f"c_{i}") for i in range(8)]  # crottles
d = [Int(f"d_{i}") for i in range(8)]  # dupples
cool = [Bool(f"cool_{i}") for i in range(8)]  # whether truck i is cooled

opt = Optimize()

# constraints for each truck
for i in range(8):
    opt.add(n[i] >= 0, n[i] <= 1)            # at most 1 nuzzle per truck
    opt.add(p[i] >= 0)                        # prittles non-negative
    opt.add(s[i] >= 0)                        # skipples non-negative
    opt.add(c[i] >= 0)                        # crottles non-negative
    opt.add(d[i] >= 0)                        # dupples non-negative
    opt.add(n[i]+p[i]+s[i]+c[i]+d[i] <= 8)   # max 8 pallets per truck
    opt.add(700*n[i] + 400*p[i] + 1000*s[i] + 2500*c[i] + 200*d[i] <= 8000)  # max weight 8000 kg
    opt.add(Implies(s[i] > 0, cool[i]))      # skipples only on cooled trucks

# other constraints
opt.add(Sum(n) == 4, Sum(s) == 8, Sum(c) == 10, Sum(d) == 20)
opt.add(Sum([If(y,1,0) for y in cool]) == 3)  # exactly 3 cooled trucks

# Part (b): prittles and crottles cannot share a truck
opt.add([Or(p[i]==0, c[i]==0) for i in range(8)])

# Objective: maximize total prittles delivered
opt.maximize(Sum(p))

# Solve and measure runtime
start_time = time.perf_counter()
result = opt.check()
end_time = time.perf_counter()
runtime = end_time - start_time

print(f"Solver runtime (s): {runtime:.4f}")
print(f"Solver status: {result}")

if result == sat:
    model = opt.model()
    total_prittles = sum(model[p[i]].as_long() for i in range(8))
    print(f"Total Prittles delivered: {total_prittles}\n")
    
    print("Truck assignments:")
    print("Truck | Nuzzles Prittles Skipples Crottles Dupples Total_Weight Cooling")
    for i in range(8):
        n_val = model[n[i]].as_long()
        p_val = model[p[i]].as_long()
        s_val = model[s[i]].as_long()
        c_val = model[c[i]].as_long()
        d_val = model[d[i]].as_long()
        total_weight = 700*n_val + 400*p_val + 1000*s_val + 2500*c_val + 200*d_val
        cool_val = model[cool[i]]
        print(f"{i+1:>5} | {n_val:>7} {p_val:>8} {s_val:>8} {c_val:>8} {d_val:>7} {total_weight:>12} {cool_val}")
else:
    print("No solution found.")
    
from z3 import *

# ---------------------------
# parameters
# ---------------------------

# parameters of poster
w = [5, 5, 4, 3, 7, 6, 5, 4, 6, 4, 6, 5]
h = [6, 6, 10, 11, 7, 10, 13, 10, 9, 15, 10, 10]
price = [10, 14, 13, 15, 10, 17, 21, 16, 16, 23, 19, 17]

# parameters of canvases
W = [12, 12]
H = [12, 12]
cost = [30, 30]


# variables of printing logic
N_canvas = 2  # number of canvases
N_poster = 12  # number of poster

# posters are printed or not
z = [[Bool(f"z_{c}_{p}") for p in range(N_poster)] for c in range(N_canvas)]

# Bottom-left coordinates
x = [[Int(f"x_{c}_{p}") for p in range(N_poster)] for c in range(N_canvas)]
y = [[Int(f"y_{c}_{p}") for p in range(N_poster)] for c in range(N_canvas)]

# posters rotate 90° or not
r = [[Bool(f"r_{c}_{p}") for p in range(N_poster)] for c in range(N_canvas)]

# canvases are used or not
u = [Bool(f"u_{c}") for c in range(N_canvas)]

s = Optimize()

# ---------------------------
# constraint
# ---------------------------

# a poster is printed at most once
for i in range(N_poster):
    s.add(Sum([If(z[p][i], 1, 0) for p in range(N_canvas)]) <= 1)

# fit in canvas
for c in range(N_canvas):
    for p in range(N_poster):
        s.add(Implies(z[c][p], Or(
            And(r[c][p] == False,
                x[c][p] >= 0,
                y[c][p] >= 0,
                x[c][p] + w[p] <= W[c],
                y[c][p] + h[p] <= H[c]),
            And(r[c][p] == True,
                x[c][p] >= 0,
                y[c][p] >= 0,
                x[c][p] + h[p] <= W[c],
                y[c][p] + w[p] <= H[c])
        )))

# no overlap and rotate
for c in range(N_canvas):
    for i in range(N_poster):
        for j in range(i+1, N_poster):
            b_left  = Bool(f"left_{c}_{i}_{j}")
            b_right = Bool(f"right_{c}_{i}_{j}")
            b_below = Bool(f"below_{c}_{i}_{j}")
            b_above = Bool(f"above_{c}_{i}_{j}")

            s.add(Implies(And(z[c][i], z[c][j]), Or(b_left, b_right, b_below, b_above)))

            # efficient height and width
            w_eff_i = If(r[c][i], h[i], w[i])
            h_eff_i = If(r[c][i], w[i], h[i])
            w_eff_j = If(r[c][j], h[j], w[j])
            h_eff_j = If(r[c][j], w[j], h[j])

            s.add(Implies(And(z[c][i], z[c][j], b_left),  x[c][i] + w_eff_i <= x[c][j]))
            s.add(Implies(And(z[c][i], z[c][j], b_right), x[c][j] + w_eff_j <= x[c][i]))
            s.add(Implies(And(z[c][i], z[c][j], b_below), y[c][i] + h_eff_i <= y[c][j]))
            s.add(Implies(And(z[c][i], z[c][j], b_above), y[c][j] + h_eff_j <= y[c][i]))

# not fit in any canvases
for c in range(N_canvas):
    for p in range(N_poster):
        if (w[p] > W[c] and h[p] > W[c]) or (h[p] > H[c] and w[p] > H[c]):
            s.add(z[c][p] == False)

# associate canvas and poster
for c in range(N_canvas):
    for p in range(N_poster):
        s.add(Implies(z[c][p], u[c]))

# ---------------------------
# calculate profit
# ---------------------------

total_profit = Sum([If(z[c][p], price[p], 0) for c in range(N_canvas) for p in range(N_poster)]) \
               - Sum([If(u[c], cost[c], 0) for c in range(N_canvas)])
h_opt = s.maximize(total_profit)


# ---------------------------
# solution
# ---------------------------
print("solving...")
res = s.check()
print("check() ->", res)

if res == sat:
    m = s.model()
    for c in range(N_canvas):
        assigned = [p for p in range(N_poster) if m.evaluate(z[c][p]) == True]
        if assigned:
            print(f"\nPrinter {c} (W={W[c]}, H={H[c]}, cost={cost[c]}):")
            for p in assigned:
                xi = m.evaluate(x[c][p])
                yi = m.evaluate(y[c][p])
                rot = m.evaluate(r[c][p])
                print(f"  Poster {p}: size=({w[p]}x{h[p]}), price={price[p]}, "
                      f"rotated={rot}, at=({xi},{yi})")
    print("\ntotal profit =", m.evaluate(total_profit))
else:
    print(res)


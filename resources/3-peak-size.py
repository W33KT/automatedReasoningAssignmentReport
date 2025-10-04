from oxidd.bdd import BDDManager

manager = BDDManager(100_000_000, 1_000_000, 1)

# Create all variables
count = 12
z = [manager.var(i) for i in manager.add_named_vars(["z"])]
x = [manager.var(i) for i in manager.add_named_vars(
    ["x"+str(i) for i in range(count)])]
y = [manager.var(i) for i in manager.add_named_vars(
    ["y"+str(i) for i in reversed(range(count))])]

# Create and visualize z
acc = z[0]
r = [(acc, "z")]

# Add bi-implications and create diagrams for some
for i in range(count):
    acc = acc & x[i].equiv(y[count-i-1])
    r += [(acc, "xy"+str(i+1))]

# Create final diagram
acc = acc & ~z[0]
r += [(acc, "z & !z")]

# Create a single visualization with all intermediate diagrams
manager.visualize_with_names("all", r)
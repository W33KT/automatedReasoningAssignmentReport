# Import the bdd manager
from oxidd.bdd import BDDManager

# Create a new manager (which represents a shared diagram), which can hold up to 100 million nodes, has an apply cache of up to 1 million entries, and uses a single thread
manager = BDDManager(100_000_000, 1_000_000, 1)

# Add variable layers to the shared diagram, and access the sub-diagrams representing each variable
x = [manager.var(i) for i in manager.add_vars(3)]

# Create some complex BDDs combining multiple variables
r1 = (x[0] & ~x[1]) | x[2]
r2 = (x[0] | ~x[1]) & x[2]

# Visualize the BDDs with an associated name
manager.visualize_with_names("r1_and_r2", [(r1, "r1"), (r2, "r2")])
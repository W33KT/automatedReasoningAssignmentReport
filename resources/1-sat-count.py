# Import the bdd manager
from oxidd.bdd import BDDManager

# Create a new manager (which represents a shared diagram), which can hold up to 100 million nodes, has an apply cache of up to 1 million entries, and uses a single thread
manager = BDDManager(100_000_000, 1_000_000, 1)

# Add variable layers to the shared diagram, and access the sub-diagrams representing each variable
x = [manager.var(i) for i in manager.add_vars(3)]

# Create some complex BDD combining multiple variables
r = (x[0] & ~x[1]) | x[2]

# Check the sat count of our BDD, by providing the number of variables in the diagram
print(r.sat_count(len(x))) # Prints 5
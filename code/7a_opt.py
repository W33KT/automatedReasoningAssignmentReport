from z3 import *
import random
import time
import json


num_tasks = 20
num_machines = 8
Pmax = 20
duration_range = (2, 10)
power_range = (1, 5)
deadline_range = (20, 50)
precedence_probability = 0.08

duration = [random.randint(*duration_range) for _ in range(num_tasks)]
power = [random.randint(*power_range) for _ in range(num_tasks)]
deadline = [random.randint(*deadline_range) for _ in range(num_tasks)]

precedences = []
for i in range(num_tasks):
    for j in range(i+1, num_tasks):
        if random.random() < 0.3:
            precedences.append((i,j))


data = {
    "num_tasks": num_tasks,
    "num_machines": num_machines,
    "Pmax": Pmax,
    "duration": duration,
    "power": power,
    "deadline": deadline,
    "precedences": precedences
}

with open("task_data.json", "w") as f:
    json.dump(data, f, indent=4)

print("Random task data saved to task_data.json\n")

print("Task | Duration | Power | Deadline")
for i in range(num_tasks):
    print(f"{i:4} | {duration[i]:8} | {power[i]:5} | {deadline[i]:8}")
print("Precedences (i->j):", precedences)
print("Pmax =", Pmax)
print("Number of Machines =", num_machines)
print("=============================\n")

start_time = time.time()

start_vars = [Int(f'start_{i}') for i in range(num_tasks)]
machine_vars = [Int(f'machine_{i}') for i in range(num_tasks)]
tardiness_vars = [Int(f'tardiness_{i}') for i in range(num_tasks)]
Cmax = Int('Cmax')

s = Optimize()

for i in range(num_tasks):
    s.add(start_vars[i] >= 0)
    s.add(machine_vars[i] >= 0, machine_vars[i] < num_machines)
    s.add(tardiness_vars[i] >= 0)

for i, j in precedences:
    s.add(start_vars[i] + duration[i] <= start_vars[j])

for i in range(num_tasks):
    for j in range(i+1, num_tasks):
        s.add(Or(machine_vars[i] != machine_vars[j],
                 start_vars[i] + duration[i] <= start_vars[j],
                 start_vars[j] + duration[j] <= start_vars[i]))

time_horizon = sum(duration)
for t in range(time_horizon):
    s.add(Sum([
        If(And(start_vars[i] <= t, t < start_vars[i] + duration[i]), power[i], 0)
        for i in range(num_tasks)
    ]) <= Pmax)

for i in range(num_tasks):
    s.add(tardiness_vars[i] >= start_vars[i] + duration[i] - deadline[i])
    s.add(tardiness_vars[i] >= 0)

for i in range(num_tasks):
    s.add(Cmax >= start_vars[i] + duration[i])

h1 = s.minimize(Cmax)

if s.check() == sat:
    m = s.model()
    best_Cmax = m[Cmax].as_long()
    print(f"Phase 1: Best Cmax = {best_Cmax}")

    s.add(Cmax == best_Cmax)
    h2 = s.minimize(Sum(tardiness_vars))

    if s.check() == sat:
        m = s.model()
        print("\nOptimal Schedule Found:")
        for i in range(num_tasks):
            print(f"Task {i}: start={m[start_vars[i]]}, machine={m[machine_vars[i]]}, tardiness={m[tardiness_vars[i]]}")
        total_tardy = sum([m[tardiness_vars[i]].as_long() for i in range(num_tasks)])
        print(f"Max Completion Time: {m[Cmax]}")
        print(f"Total Tardiness: {total_tardy}")
    else:
        print("No feasible schedule found in Phase 2.")
else:
    print("No feasible schedule found in Phase 1.")

end_time = time.time()
print(f"Elapsed time: {end_time - start_time:.6f} seconds")

import matplotlib.pyplot as plt


tasks = []
for i in range(num_tasks):
    start = m[start_vars[i]].as_long()
    end = start + duration[i]
    machine = m[machine_vars[i]].as_long()
    tasks.append((i, machine, start, end))


fig, ax = plt.subplots(figsize=(10, 5))
colors = plt.cm.get_cmap('tab20', num_tasks)

for (i, machine, start, end) in tasks:
    ax.barh(y=machine, width=end - start, left=start, height=0.6,
            color=colors(i), edgecolor='black', label=f"Task {i}" if i < 20 else "")
    ax.text(start + (end - start)/2, machine, f"T{i}",
            ha='center', va='center', color='white', fontsize=8)

ax.set_xlabel("Time")
ax.set_ylabel("Machine ID")
ax.set_title("Z3 Task Scheduling Gantt Chart")
ax.grid(True, axis='x', linestyle='--', alpha=0.6)

plt.tight_layout()
plt.show()


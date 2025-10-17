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

# generate data
duration = [random.randint(*duration_range) for _ in range(num_tasks)]
power = [random.randint(*power_range) for _ in range(num_tasks)]
deadline = [random.randint(*deadline_range) for _ in range(num_tasks)]

# generate precedences
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
print("Generated Task Data:")
print("Task | Duration | Power | Deadline")
for i in range(num_tasks):
    print(f"{i:4} | {duration[i]:8} | {power[i]:5} | {deadline[i]:8}")
print("Precedences (i->j):", precedences)
print("Pmax =", Pmax)
print("Number of Machines =", num_machines)
print("=============================\n")



start_time = time.time()

start = [Int(f'start_{i}') for i in range(num_tasks)]
machine = [Int(f'machine_{i}') for i in range(num_tasks)]
tardiness = [Int(f'tardiness_{i}') for i in range(num_tasks)]
Cmax = Int('Cmax')

s = Optimize()

for i in range(num_tasks):
    s.add(start[i] >= 0)
    s.add(machine[i] >= 0, machine[i] < num_machines)
    s.add(tardiness[i] >= 0)

for i, j in precedences:
    s.add(start[i] + duration[i] <= start[j])

for i in range(num_tasks):
    for j in range(i + 1, num_tasks):
        s.add(Or(machine[i] != machine[j],
                 start[i] + duration[i] <= start[j],
                 start[j] + duration[j] <= start[i]))

time_horizon = sum(duration)
for t in range(time_horizon):
    s.add(Sum([If(And(start[i] <= t, t < start[i] + duration[i]), power[i], 0)
               for i in range(num_tasks)]) <= Pmax)

for i in range(num_tasks):
    s.add(tardiness[i] >= start[i] + duration[i] - deadline[i])
    s.add(tardiness[i] >= 0)

def z3_max(lst):
    if len(lst) == 1:
        return lst[0]
    else:
        return If(lst[0] > z3_max(lst[1:]), lst[0], z3_max(lst[1:]))

s.add(Cmax == z3_max([start[i] + duration[i] for i in range(num_tasks)]))


s.minimize(Cmax)
s.minimize(Sum(tardiness))

if s.check() == sat:
    m = s.model()
    print("Schedule found:")
    for i in range(num_tasks):
        print(f"Task {i}: start={m[start[i]]}, machine={m[machine[i]]}, tardiness={m[tardiness[i]]}")
    print(f"Max Completion Time: {m[Cmax]}")
    total_tardy = sum([m[tardiness[i]].as_long() for i in range(num_tasks)])
    print(f"Total Tardiness: {total_tardy}")
else:
    print("No feasible schedule found.")

end_time = time.time()
print(f"Elapsed time: {end_time - start_time:.6f} seconds")

import matplotlib.pyplot as plt


tasks = []
for i in range(len(start)):
    start_time_task = m[start[i]].as_long()
    end_time_task = start_time_task + duration[i]
    machine_id = m[machine[i]].as_long()
    tasks.append((i, machine_id, start_time_task, end_time_task))


fig, ax = plt.subplots(figsize=(10, 5))
colors = plt.get_cmap('tab20', len(tasks))

for (i, machine_id, start_time_task, end_time_task) in tasks:
    ax.barh(
        y=machine_id,
        width=end_time_task - start_time_task,
        left=start_time_task,
        height=0.6,
        color=colors(i),
        edgecolor='black'
    )
    ax.text(
        start_time_task + (end_time_task - start_time_task)/2,
        machine_id,
        f"T{i}",
        ha='center', va='center',
        color='white', fontsize=8
    )

ax.set_xlabel("Time")
ax.set_ylabel("Machine ID")
ax.set_title("Z3 Task Scheduling Gantt Chart")
ax.set_yticks(range(num_machines))
ax.set_yticklabels([f"M{m}" for m in range(num_machines)])
ax.grid(True, axis='x', linestyle='--', alpha=0.6)

plt.tight_layout()
plt.savefig("gantt_chart.png", dpi=300)
plt.show()

from z3 import *
import itertools
import time


N = 10  # number of people
H = 5   # number of houses
T = 5   # number of courses


couple_of = {2*h: h for h in range(H)}
couple_of.update({2*h+1: h for h in range(H)})
house_members = {h: (2*h, 2*h+1) for h in range(H)}

def solve_instance(require_p1=False, require_p2=False, require_p3=False, require_p4=False, timeout_ms=None):
    # serve[h][k] = True if house h hosts course k
    serve = [[Bool(f"serve_{h}_{k}") for k in range(T)] for h in range(H)]
    # attend[p][k] = h when people p attends course k at house h
    attend = [[Int(f"attend_{p}_{k}") for k in range(T)] for p in range(N)]

    s = Solver()
    if timeout_ms is not None:
        s.set("timeout", timeout_ms)

    # People attendance must be a valid house number
    for p in range(N):
        for k in range(T):
            s.add(attend[p][k] >= 0, attend[p][k] < H)

    # Each course is hosted in exactly 2 houses; each house hosts exactly 2 courses
    for k in range(T):
        s.add(Sum([If(serve[h][k], 1, 0) for h in range(H)]) == 2)
    for h in range(H):
        s.add(Sum([If(serve[h][k], 1, 0) for k in range(T)]) == 2)

    # Couples must attend their own house when hosting
    for h in range(H):
        a, b = house_members[h]
        for k in range(T):
            s.add(Implies(serve[h][k], attend[a][k] == h))
            s.add(Implies(serve[h][k], attend[b][k] == h))

    # Each person attends exactly one house per course
    for p in range(N):
        for k in range(T):
            s.add(Sum([If(attend[p][k] == h, 1, 0) for h in range(H)]) == 1)

    # A person can only attend a house if that house is hosting the course
    for p in range(N):
        for k in range(T):
            for h in range(H):
                s.add(Implies(attend[p][k] == h, serve[h][k]))

    # 6. Each hosting house must have exactly 5 people (couple + 3 guests)
    for h in range(H):
        for k in range(T):
            s.add(Sum([If(attend[p][k] == h, 1, 0) for p in range(N)]) == If(serve[h][k], 5, 0))

    # 7. property 4: Distinct guests
    for h in range(H):
        members = set(house_members[h])
        for p in range(N):
            if p in members:
                continue
            s.add(Sum([If(And(serve[h][k], attend[p][k] == h), 1, 0) for k in range(T)]) <= (1 if require_p4 else 2))

    # 8. property 3: Couples never meet outside their own house
    if require_p3:
        for h in range(H):
            a, b = house_members[h]
            for k in range(T):
                s.add(Implies(attend[a][k] == attend[b][k], attend[a][k] == h))

    # 9. Meeting counts between each two people
    meet = {}
    for i, j in itertools.combinations(range(N), 2):
        meet[(i,j)] = Sum([If(attend[i][k] == attend[j][k], 1, 0) for k in range(T)])
        # each pair meets at most 4 times
        s.add(meet[(i,j)] <= 4)

    # 10. property 1: Each pair meets at least once
    if require_p1:
        for (i,j), m in meet.items():
            s.add(m >= 1)

    # 11. property 2: Each pair meets at most 3 times
    if require_p2:
        for (i,j), m in meet.items():
            s.add(m <= 3)

    
    t0 = time.perf_counter()
    ok = s.check()
    t1 = time.perf_counter()
    runtime = t1 - t0

    if ok == sat:
        m = s.model()
        schedule = {k: [h for h in range(H) if m.evaluate(serve[h][k])] for k in range(T)}
        attendees = {(h,k): [p for p in range(N) if m.evaluate(attend[p][k]).as_long() == h] for k in range(T) for h in range(H)}
        meet_counts = { (i,j): m.evaluate(meet[(i,j)]).as_long() for (i,j) in meet.keys() }

        return {
            "sat": True,
            "model": m,
            "runtime": runtime,
            "schedule": schedule,
            "attendees": attendees,
            "meet_counts": meet_counts,
            "serve_matrix": [[is_true(m.evaluate(serve[h][k])) for k in range(T)] for h in range(H)],
            "attend_matrix": [[m.evaluate(attend[p][k]).as_long() for k in range(T)] for p in range(N)],
        }
    else:
        return {"sat": False, "status": ok, "runtime": runtime}


def print_solution(sol):
    if not sol["sat"]:
        print("No solution:", sol["status"], "runtime", sol["runtime"])
        return
    print(f"Solver runtime: {sol['runtime']:.4f} s")
    print("\nCourses (t): houses serving")
    for t in range(T):
        houses = sol["schedule"][t]
        print(f" Course {t}: houses {houses}")
    print("\nHouse attendees (house h at course t):")
    for t in range(T):
        for h in sol["schedule"][t]:
            att = sol["attendees"][(h,t)]
            print(f"  (course {t}, house {h}): {att}")
    print("\nMeeting counts (pair -> times met):")
    for (i,j), v in sorted(sol["meet_counts"].items()):
        print(f" {i}-{j}: {v}", end=";")
    print("\n\nAttend matrix (rows persons 0..9, cols courses 0..4):")
    for i,row in enumerate(sol["attend_matrix"]):
        print(f"{i}: {row}")


if __name__ == "__main__":
    # Scenario A1: property1 + property3
    print("=== Scenario A1: property1 (every pair meets at least once) + property3 (couples never meet outside their own houses) ===")
    sol_a1 = solve_instance(require_p1=True, require_p3=True, require_p4=False, timeout_ms=60000)
    print_solution(sol_a1)

    # Scenario A2: property1 + property4
    print("\n=== Scenario A2: property1 + property4 (6 guests distinct per house) ===")
    sol_a2 = solve_instance(require_p1=True, require_p3=False, require_p4=True, timeout_ms=60000)
    print_solution(sol_a2)

    # Scenario A3: property1 + property3 + property4
    print("\n=== Scenario A3: property1 + property3 + property4 (expected UNSAT) ===")
    sol_a3 = solve_instance(require_p1=True, require_p3=True, require_p4=True, timeout_ms=60000)
    if sol_a3["sat"]:
        print("WARNING: Found a model (contradicts expected impossibility):")
        print_solution(sol_a3)
    else:
        print("No solution as expected. Status:", sol_a3["status"], "runtime:", sol_a3["runtime"])

    # Scenario B: property2 + property3 + property4
    print("\n=== Scenario B: property2 (every pair meets at most 3 times) + property3 + property4 ===")
    sol_b = solve_instance(require_p1=False, require_p2=True, require_p3=True, require_p4=True, timeout_ms=60000)
    print_solution(sol_b)

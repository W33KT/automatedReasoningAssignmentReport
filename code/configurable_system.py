import os
import random
import time
from oxidd.bdd import BDDManager
from multiprocessing import cpu_count
from collections import Counter
from z3 import Solver, Bool, Not, Or, And, Tactic, Goal, Then

def parse_dimacs_cnf(file_path):
    clauses, var_freq = [], Counter()
    num_vars, max_var = 0, 0
    try:
        with open(file_path, 'r') as f:
            for line in f:
                line, *_ = line.split(' c ')
                line = line.strip()
                if not line or line.startswith('c'): continue
                parts = line.split()
                if line.startswith('p'):
                    num_vars = int(parts[2])
                    continue
                clause = [int(lit) for lit in parts if lit != '0']
                if clause:
                    clauses.append(clause)
                    max_var = max(max_var, max(abs(lit) for lit in clause))
                    for lit in clause:
                        var_freq[abs(lit) - 1] += 1
    except Exception as e:
        raise ValueError(f"Error parsing {file_path}: {e}")
    effective_num_vars = max(num_vars, max_var)
    return effective_num_vars, clauses, var_freq

def simplify_with_z3(num_vars, clauses):
    z3_vars = [Bool(f'x_{i+1}') for i in range(num_vars)]
    
    g = Goal()
    for clause in clauses:
        g.add(Or([z3_vars[abs(lit)-1] if lit > 0 else Not(z3_vars[abs(lit)-1]) for lit in clause]))

    tactic = Then(Tactic('simplify'), Tactic('tseitin-cnf'))
    simplified_goal = tactic(g)
    
    simplified_clauses = []
    if len(simplified_goal) > 0:
        for clause_expr in simplified_goal[0]:
            new_clause = []
            
            children = []
            if clause_expr.decl().name() == 'or':
                children = clause_expr.children()
            else:
                children = [clause_expr]
            
            for lit_expr in children:
                is_neg = lit_expr.decl().name() == 'not'
                var_expr = lit_expr.arg(0) if is_neg else lit_expr
                var_num = int(var_expr.decl().name().split('_')[1])
                new_clause.append(-var_num if is_neg else var_num)
            simplified_clauses.append(new_clause)
        
    return simplified_clauses

def get_force_order(num_vars, hyperedges):
    l = list(range(num_vars))
    for _ in range(100):
        cog = [sum(l[v] for v in e if v < num_vars) / len(e) if e else 0 for e in hyperedges]
        l_new, counts = [0.0] * num_vars, [0] * num_vars
        for i, e in enumerate(hyperedges):
            for v in e:
                if v < num_vars:
                    l_new[v] += cog[i]; counts[v] += 1
        for v in range(num_vars):
            if counts[v] > 0: l_new[v] /= counts[v]
        sorted_vars = sorted(range(num_vars), key=lambda v: l_new[v])
        new_l = [0] * num_vars
        for pos, v in enumerate(sorted_vars): new_l[v] = pos
        l = new_l
    return sorted(range(num_vars), key=lambda v: l[v])

def build_bdd_from_cnf(manager, num_vars, clauses):
    hyperedges = [{abs(lit) - 1 for lit in clause} for clause in clauses]
    var_order = get_force_order(num_vars, hyperedges)
    manager.add_vars(num_vars)
    vars_list = [manager.var(i) for i in range(num_vars)]
    manager.set_var_order(var_order)
    
    bdd = manager.true()
    chunk_size = 100
    for i in range(0, len(clauses), chunk_size):
        chunk_bdd = manager.true()
        for clause in clauses[i:i + chunk_size]:
            clause_bdd_inner = manager.false()
            for lit in clause:
                v_idx = abs(lit) - 1
                if v_idx < num_vars:
                    v = vars_list[v_idx]
                    clause_bdd_inner |= v if lit > 0 else ~v
            chunk_bdd &= clause_bdd_inner
        bdd &= chunk_bdd
        if bdd == manager.false():
            print("Warning: BDD became unsatisfiable during construction.")
            break
    return bdd, vars_list

def weighted_random_sample_slow_but_stable(manager, bdd, vars_list, k, num_vars):
    if not bdd.satisfiable(): return []
    samples = set()
    print("  Starting sampling (slow but stable method)...")
    for i in range(k * 10):
        if len(samples) >= k: break
        if i > 0 and i % 100 == 0:
             print(f"  (Sampling progress: {len(samples)}/{k} samples found...)")

        assignment, current = [], bdd
        for j in range(num_vars):
            if current == manager.true() or current == manager.false():
                for l in range(j, num_vars):
                    assignment.append(random.randint(0,1))
                break
            low, high = current.cofactor_false(), current.cofactor_true()
            low_count = low.sat_count(num_vars - j - 1) if low else 0
            high_count = high.sat_count(num_vars - j - 1) if high else 0
            total = low_count + high_count
            if total == 0:
                assignment = []
                break
            if random.random() < low_count / total:
                assignment.append(0); current = low
            else:
                assignment.append(1); current = high
        if len(assignment) == num_vars:
            samples.add(tuple(assignment))
    return list(samples)

def find_one_solution_compatible(manager, bdd, vars_list, num_vars):
    if not bdd.satisfiable(): return None
    assignment, current_bdd = {}, bdd
    while not (current_bdd == manager.true() or current_bdd == manager.false()):
        var_index = current_bdd.var()
        low_child = current_bdd.cofactor_false()
        if low_child.satisfiable():
            assignment[var_index] = 0; current_bdd = low_child
        else:
            assignment[var_index] = 1; current_bdd = current_bdd.cofactor_true()
    final_assignment = [assignment.get(i, 0) for i in range(num_vars)]
    return tuple(final_assignment)

def count_pairwise_simplified(manager, bdd, vars_list, num_vars, var_freq):
    total, max_vars = 0, min(num_vars, 50)
    high_freq_vars_indices = [v_idx for v_idx, _ in var_freq.most_common(max_vars)]
    for i in range(len(high_freq_vars_indices)):
        for j in range(i + 1, len(high_freq_vars_indices)):
            idx1, idx2 = high_freq_vars_indices[i], high_freq_vars_indices[j]
            var1, var2 = vars_list[idx1], vars_list[idx2]
            for lit1 in (var1, ~var1):
                for lit2 in (var2, ~var2):
                    if (bdd & lit1 & lit2).satisfiable():
                        total += 1
    return total

def get_cover_size_simplified(manager, bdd, vars_list, num_vars, var_freq):
    _find_one = find_one_solution_compatible
    max_vars = min(num_vars, 50)
    high_freq_vars_indices = [v_idx for v_idx, _ in var_freq.most_common(max_vars)]
    universe = set()
    for i in range(len(high_freq_vars_indices)):
        for j in range(i + 1, len(high_freq_vars_indices)):
            idx1, idx2 = high_freq_vars_indices[i], high_freq_vars_indices[j]
            var1, var2 = vars_list[idx1], vars_list[idx2]
            for val1, lit1 in enumerate((~var1, var1)):
                for val2, lit2 in enumerate((~var2, var2)):
                    if (bdd & lit1 & lit2).satisfiable():
                        universe.add(((idx1, val1), (idx2, val2)))
    if not universe: return 0
    cover_set, uncovered = [], universe
    while uncovered:
        pair = uncovered.pop()
        (i, val_i), (j, val_j) = pair
        lit_i = vars_list[i] if val_i else ~vars_list[i]
        lit_j = vars_list[j] if val_j else ~vars_list[j]
        restricted_bdd = bdd & lit_i & lit_j
        config_tuple = _find_one(manager, restricted_bdd, vars_list, num_vars)
        if config_tuple:
            cover_set.append(config_tuple)
            uncovered.difference_update({p for p in uncovered if len(config_tuple) > p[0][0] and len(config_tuple) > p[1][0] and config_tuple[p[0][0]] == p[0][1] and config_tuple[p[1][0]] == p[1][1]})
    return len(cover_set)

if __name__ == "__main__":
    script_dir = os.path.dirname(os.path.abspath(__file__))
    dir_path = os.path.abspath(os.path.join(script_dir, '..', 'resources', 'conf-dimacs'))
    if not os.path.exists(dir_path): exit(f"Error: Directory not found: {dir_path}")
    files = [f for f in os.listdir(dir_path) if f.endswith(('.cnf', '.dimacs'))]

    for file in sorted(files):
        print(f"--- Processing {file} ---")
        try:
            total_start_time = time.time()
            manager = BDDManager(500_000_000, 50_000_000, cpu_count())

            num_vars, clauses, var_freq = parse_dimacs_cnf(os.path.join(dir_path, file))
            print(f"Parsing done. Vars: {num_vars}, Original clauses: {len(clauses)}")
            
            print("Simplifying CNF with Z3 pre-processor...")
            z3_start_time = time.time()
            simplified_clauses = simplify_with_z3(num_vars, clauses)
            print(f"Z3 simplification finished in {time.time() - z3_start_time:.2f}s. New clauses: {len(simplified_clauses)}")
            
            start_time = time.time()
            phi, vars_list = build_bdd_from_cnf(manager, num_vars, simplified_clauses)
            print(f"BDD build finished in {time.time() - start_time:.2f}s.")
            
            node_count = phi.node_count()
            print(f"(i) BDD nodes: {node_count}")

            V_size = phi.sat_count(num_vars)
            print(f"(ii) |V|: {V_size}")

            print("Starting (iii) Uniform Random Sampling (Slow but Stable Method)...")
            start_time = time.time()
            A = weighted_random_sample_slow_but_stable(manager, phi, vars_list, 10000, num_vars)
            if num_vars > 41:
                k1 = sum(1 for c in A if len(c) > 41 and c[41] == 1)
                k0 = len(A) - k1
                ratio = k1 / k0 if k0 > 0 else float('inf')
            else: ratio = "N/A"
            print(f"URS finished in {time.time() - start_time:.2f}s.")
            print(f"(iii) Ratio k1/k0 for x42: {ratio}")

            print("Starting (iv) Pairwise Interactions (Simplified Strategy)...")
            start_time = time.time()
            num_pairs_simplified = count_pairwise_simplified(manager, phi, vars_list, num_vars, var_freq)
            print(f"Simplified count finished in {time.time() - start_time:.2f}s.")
            print(f"(iv) Pairwise interactions (Simplified, top 50 vars): {num_pairs_simplified}")
            
            print("Starting (v) Pairwise Cover (Simplified Strategy)...")
            start_time = time.time()
            B_size_simplified = get_cover_size_simplified(manager, phi, vars_list, num_vars, var_freq)
            print(f"Simplified cover finished in {time.time() - start_time:.2f}s.")
            print(f"(v) |B| size (Simplified, top 50 vars): {B_size_simplified}")

        except MemoryError:
            print(f"\nFATAL MEMORY ERROR for {file}.")
        except Exception as e:
            print(f"An unexpected error occurred while processing {file}: {e}")
        
        print(f"--- Total time for {file}: {time.time() - total_start_time:.2f} seconds ---\n")
import os
import random
import time
from collections import defaultdict, Counter
from oxidd.bdd import BDDManager

def parse_dimacs_cnf(file_path):
    """Parse a DIMACS CNF file, return max variable index, clauses, and var order."""
    clauses = []
    num_vars = 0
    max_var = 0
    var_freq = Counter()
    try:
        with open(file_path, 'r') as f:
            for line in f:
                line = line.strip()
                if line.startswith('c') or not line:
                    continue
                parts = line.split()
                if line.startswith('p'):
                    num_vars = int(parts[2])
                    continue
                clause = [int(lit) for lit in parts if lit != '0']
                if clause:
                    clauses.append(clause)
                    max_lit = max(abs(lit) for lit in clause)
                    max_var = max(max_var, max_lit)
                    for lit in clause:
                        var_freq[abs(lit) - 1] += 1
    except FileNotFoundError:
        raise FileNotFoundError(f"File {file_path} not found")
    except Exception as e:
        raise ValueError(f"Error parsing {file_path}: {e}")
    effective_num_vars = max(num_vars, max_var) if max_var > 0 else num_vars
    if effective_num_vars == 0:
        raise ValueError(f"No valid variables found in {file_path}")
    var_order = [v for v, _ in var_freq.most_common()]
    return effective_num_vars, clauses, var_order

def build_bdd_from_cnf(manager, num_vars, clauses, var_order):
    """Build a BDD from CNF clauses with variable ordering, in chunks."""
    start_time = time.time()
    manager.add_vars(num_vars)
    if var_order:
        manager.set_var_order(var_order)
    vars_list = [manager.var(i) for i in range(num_vars)]
    bdd = manager.true()
    invalid_literals = 0
    chunk_size = 100
    for i in range(0, len(clauses), chunk_size):
        chunk_bdd = manager.true()
        for clause in clauses[i:i + chunk_size]:
            clause_bdd = manager.false()
            valid_clause = False
            for lit in clause:
                v_idx = abs(lit) - 1
                if v_idx >= num_vars:
                    invalid_literals += 1
                    continue
                valid_clause = True
                v = vars_list[v_idx]
                clause_bdd = clause_bdd | (v if lit > 0 else ~v)
            if valid_clause:
                chunk_bdd = chunk_bdd & clause_bdd
                if not chunk_bdd.satisfiable():
                    print(f"Warning: Chunk {i//chunk_size + 1} became unsatisfiable")
                    break
        bdd = bdd & chunk_bdd
        if not bdd.satisfiable():
            print("Warning: BDD became unsatisfiable during construction")
            break
    if invalid_literals > 0:
        print(f"Warning: Skipped {invalid_literals} invalid literals")
    print(f"BDD build time: {time.time() - start_time:.2f} seconds, nodes: {bdd.node_count()}")
    return bdd, vars_list

def uniform_random_sample(manager, bdd, vars_list, k, num_vars):
    """Generate k distinct uniform random valid configurations using pick_cube."""
    start_time = time.time()
    if not bdd.satisfiable():
        raise ValueError("Cannot sample from unsatisfiable BDD")
    samples = set()
    while len(samples) < k:
        cube = bdd.pick_cube()
        if cube is None:
            continue
        assignment = [0] * num_vars
        for i in range(num_vars):
            if i in cube:
                assignment[i] = 1 if cube[i] else 0
        samples.add(tuple(assignment))
    print(f"Sampling time (k={k}): {time.time() - start_time:.2f} seconds")
    return list(samples)

def count_pairwise_interactions(manager, bdd, vars_list, num_vars):
    """Count valid pairwise interactions, limited to first 50 variables."""
    start_time = time.time()
    total = 0
    max_vars = min(num_vars, 50)
    for i in range(max_vars):
        for j in range(i + 1, max_vars):
            for v1 in [0, 1]:
                for v2 in [0, 1]:
                    restricted = bdd
                    restricted = restricted & (~vars_list[i] if v1 == 0 else vars_list[i])
                    restricted = restricted & (~vars_list[j] if v2 == 0 else vars_list[j])
                    restricted = restricted.exists(set(range(num_vars)) - {i, j})
                    if restricted.sat_count(2) > 0:
                        total += 1
    print(f"Pairwise interaction time: {time.time() - start_time:.2f} seconds")
    return total

def small_pairwise_cover(manager, bdd, vars_list, num_vars):
    """Greedy pairwise cover with optimized sampling."""
    start_time = time.time()
    max_vars = min(num_vars, 50)
    universe = set()
    for i in range(max_vars):
        for j in range(i + 1, max_vars):
            for v1 in [0, 1]:
                for v2 in [0, 1]:
                    restricted = bdd
                    restricted = restricted & (~vars_list[i] if v1 == 0 else vars_list[i])
                    restricted = restricted & (~vars_list[j] if v2 == 0 else vars_list[j])
                    restricted = restricted.exists(set(range(num_vars)) - {i, j})
                    if restricted.sat_count(2) > 0:
                        universe.add((i, v1, j, v2))
    covered = set()
    B_size = 0
    max_attempts = 100
    sample_size = 5
    while covered != universe and max_attempts > 0:
        best_new_count = 0
        best_config = None
        for _ in range(sample_size):
            config = uniform_random_sample(manager, bdd, vars_list, 1, num_vars)[0]
            new_count = sum(1 for (x, vx, y, vy) in universe
                            if config[x] == vx and config[y] == vy and (x, vx, y, vy) not in covered)
            if new_count > best_new_count:
                best_new_count = new_count
                best_config = config
        if best_new_count == 0:
            max_attempts -= 1
            continue
        B_size += 1
        for pair in universe:
            (x, vx, y, vy) = pair
            if best_config[x] == vx and config[y] == vy:
                covered.add(pair)
        max_attempts -= 1
    print(f"Pairwise cover time: {time.time() - start_time:.2f} seconds")
    return B_size

# Main execution
if __name__ == "__main__":
    script_dir = os.path.dirname(os.path.abspath(__file__))
    dir_path = os.path.abspath(os.path.join(script_dir, '..', 'resources', 'conf-dimacs'))
    if not os.path.exists(dir_path):
        print(f"Directory {dir_path} does not exist")
        exit(1)
    files = [f for f in os.listdir(dir_path) if f.endswith(('.cnf', '.dimacs'))]
    if not files:
        print(f"No DIMACS files found in {dir_path}")
        exit(1)
    
    for file in sorted(files):
        try:
            start_time = time.time()
            manager = BDDManager(500_000_000, 50_000_000, 8)
            full_path = os.path.join(dir_path, file)
            num_vars, clauses, var_order = parse_dimacs_cnf(full_path)
            print(f"Processing {file}: num_vars={num_vars}, clauses={len(clauses)}")
            phi, vars_list = build_bdd_from_cnf(manager, num_vars, clauses, var_order)
            node_count = phi.node_count()
            print(f"Node count time: {time.time() - start_time:.2f} seconds")
            V_size = phi.sat_count(num_vars)
            print(f"Valid config count time: {time.time() - start_time:.2f} seconds, V_size={V_size}")
            A = uniform_random_sample(manager, phi, vars_list, 10000, num_vars)
            k1 = sum(1 for c in A if len(c) > 41 and c[41] == 1)
            k0 = len(A) - k1
            ratio = k1 / k0 if k0 > 0 else float('inf')
            num_pairs = count_pairwise_interactions(manager, phi, vars_list, num_vars)
            B_size = small_pairwise_cover(manager, phi, vars_list, num_vars)
            print(f"File: {file}")
            print(f"(i) BDD nodes: {node_count}")
            print(f"(ii) |V|: {V_size}")
            print(f"(iii) Ratio k1/k0 (x42): {ratio:.4f}")
            print(f"(iv) Pairwise interactions: {num_pairs}")
            print(f"(v) |B|: {B_size}")
            print(f"Total time for {file}: {time.time() - start_time:.2f} seconds")
            print("---")
            manager.collect()
        except MemoryError:
            print(f"Error processing {file}: Out of memory")
            print("---")
        except Exception as e:
            print(f"Error processing {file}: {e}")
            print("---")
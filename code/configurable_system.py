import sys
import random
from pathlib import Path
from itertools import combinations
from typing import List, Tuple, Dict, Optional, Set
from multiprocessing import cpu_count

try:
    from tqdm import tqdm
except ImportError:
    def tqdm(iterator, *args, **kwargs): return iterator

from oxidd.bdd import BDDManager

def parse_dimacs(file_path: Path) -> Tuple[int, List[List[int]], Optional[List[int]]]:
    num_vars, clauses, var_order = 0, [], None
    with open(file_path, 'r', encoding='latin-1') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('%'): continue
            if line.startswith('c'):
                if line.startswith('c vo '): var_order = [int(v) for v in line[5:].strip().split()]
                continue
            if line.startswith('p cnf'):
                parts = line.split(); num_vars = int(parts[2]); continue
            try:
                literals = [int(lit) for lit in line.split() if lit != '0']
                if literals: clauses.append(literals)
            except ValueError: pass
    return num_vars, clauses, var_order

class ConfigSystemAnalyzer:
    def __init__(self, file_path: Path):
        self.file_path = file_path
        self.num_vars, self.clauses, var_order = parse_dimacs(self.file_path)
        print(f"Parsing complete: {self.num_vars} variables, {len(self.clauses)} clauses.")

        self.manager = BDDManager(2**26, 2**24, cpu_count())
        self.manager.add_vars(self.num_vars)
        self.vars_list = [self.manager.var(i) for i in range(self.num_vars)]

        if var_order:
            print("Recommended variable order detected, applying it for BDD construction.")
            var_id_to_index = {var_id: var_id - 1 for var_id in range(1, self.num_vars + 1)}
            final_order = [var_id_to_index[var_id] for var_id in var_order if var_id in var_id_to_index]
            remaining_vars = [i for i in range(self.num_vars) if i not in final_order]
            self.manager.set_var_order(final_order + remaining_vars)
        else:
            print("No variable order detected, using default order.")
        
        self.phi_bdd = self._build_bdd()

    def _build_bdd(self):
        print("Building BDD...")
        phi = self.manager.true()
        for clause in tqdm(self.clauses, desc="Processing clauses"):
            clause_bdd = self.manager.false()
            for lit in clause:
                var_index = abs(lit) - 1
                if 0 <= var_index < self.num_vars:
                    var_node = self.vars_list[var_index]
                    clause_bdd |= var_node if lit > 0 else ~var_node
            phi &= clause_bdd
        print("BDD construction complete.")
        return phi

    def report_i_bdd_nodes(self):
        node_count = self.phi_bdd.node_count()
        print(f"(i) Total BDD nodes: {node_count:,}")
        return node_count

    def report_ii_valid_configurations(self):
        count = self.phi_bdd.sat_count(self.num_vars)
        try:
            count_str = f"{count:,.0f} ({count:.2e})"
        except (OverflowError, ValueError):
            count_str_val = str(count)
            magnitude = len(count_str_val)
            count_str = f"{count_str_val[:30]}... (approx. {magnitude} digits)"
        print(f"(ii) Total valid configurations |V|: {count_str}")
        return count
    
    def _sample_one_uniform(self, bdd_func):
        if not bdd_func.satisfiable(): return None
        assignment = [0] * self.num_vars
        current = bdd_func
        processed_levels = set()

        while not (current == self.manager.true() or current == self.manager.false()):
            var_level = current.node_level()
            if var_level is None:
                break

            low = current.cofactor_false()
            high = current.cofactor_true()
            
            remaining_vars_count = self.num_vars - var_level - 1
            low_count = low.sat_count(remaining_vars_count)
            high_count = high.sat_count(remaining_vars_count)
            total = low_count + high_count
            if total == 0: return None

            if random.randrange(total) < low_count:
                assignment[var_level] = 0
                current = low
            else:
                assignment[var_level] = 1
                current = high
            processed_levels.add(var_level)

        for i in range(self.num_vars):
            if i not in processed_levels:
                assignment[i] = random.randint(0, 1)
        return tuple(assignment)

    def report_iii_urs_ratio(self, k=10000, var_index_1_based=42):
        print(f"Starting Uniform Random Sampling (URS) for {k} samples...")
        if not self.phi_bdd.satisfiable():
             print("(iii) Ratio: 0/0 (No valid configurations)"); return "0/0"
        
        samples, pbar = set(), tqdm(total=k, desc="URS Sampling")
        for _ in range(k * 20 + 100):
            if len(samples) >= k: break
            sample = self._sample_one_uniform(self.phi_bdd)
            if sample and sample not in samples:
                samples.add(sample); pbar.update(1)
        pbar.close()

        if not samples: print("(iii) Ratio: 0/0 (Could not generate samples)"); return "0/0"
        if len(samples) < k: print(f"\nWarning: Sampling ended early. Found only {len(samples)}/{k} unique samples.")

        var_index_0_based = var_index_1_based - 1
        if 0 <= var_index_0_based < self.num_vars:
            k1 = sum(1 for c in samples if c[var_index_0_based] == 1)
            k0 = len(samples) - k1
            ratio_str = f"{k1}/{k0}" if k0 != 0 else f"{k1}/0 (inf)"
        else:
            ratio_str = "N/A (Variable not in model)"
        print(f"(iii) Selection ratio for x{var_index_1_based} (k={len(samples)}): k1/k0 = {ratio_str}")
        return ratio_str

    def report_iv_pairwise_interactions(self):
        print("Calculating all valid pairwise interactions...")
        total_interactions = 0
        for i in tqdm(range(self.num_vars), desc="Calculating pairs"):
            for j in range(i + 1, self.num_vars):
                var_i, var_j = self.vars_list[i], self.vars_list[j]
                if (self.phi_bdd & var_i & var_j).satisfiable(): total_interactions += 1
                if (self.phi_bdd & var_i & ~var_j).satisfiable(): total_interactions += 1
                if (self.phi_bdd & ~var_i & var_j).satisfiable(): total_interactions += 1
                if (self.phi_bdd & ~var_i & ~var_j).satisfiable(): total_interactions += 1
        print(f"(iv) Total valid pairwise interactions: {total_interactions:,}")
        return total_interactions

    def report_v_pairwise_cover_size(self):
        print("Generating pairwise interaction cover set using a greedy algorithm...")
        uncovered, cover_set = set(), []
        print("  - Generating the universe of pairs to cover...")
        for i in tqdm(range(self.num_vars), desc="Generating pairs"):
            for j in range(i + 1, self.num_vars):
                var_i, var_j = self.vars_list[i], self.vars_list[j]
                # val_i/val_j: 0 for false, 1 for true
                for val_i, lit_i in enumerate((~var_i, var_i)):
                    for val_j, lit_j in enumerate((~var_j, var_j)):
                        if (self.phi_bdd & lit_i & lit_j).satisfiable():
                            # Ensure a canonical representation for the pair to avoid duplicates.
                            p1, p2 = (i, val_i), (j, val_j)
                            uncovered.add(tuple(sorted((p1, p2))))
        
        if not uncovered: print("(v) Pairwise cover set size |B|: 0"); return 0

        pbar = tqdm(total=len(uncovered), desc="Building cover set")
        while uncovered:
            pair_to_cover = next(iter(uncovered))
            (i, val_i), (j, val_j) = pair_to_cover
            lit_i = self.vars_list[i] if val_i else ~self.vars_list[i]
            lit_j = self.vars_list[j] if val_j else ~self.vars_list[j]
            restricted_bdd = self.phi_bdd & lit_i & lit_j
            
            solution = self._sample_one_uniform(restricted_bdd)
            
            if solution:
                cover_set.append(solution)
                covered_by_new = set()
                for p in uncovered:
                    (p_i, p_val_i), (p_j, p_val_j) = p
                    if solution[p_i] == p_val_i and solution[p_j] == p_val_j:
                        covered_by_new.add(p)
                
                update_amount = len(covered_by_new)
                uncovered -= covered_by_new
                pbar.update(update_amount)
            else:
                 uncovered.remove(pair_to_cover); pbar.update(1)
        pbar.close()

        size_B = len(cover_set)
        print(f"(v) Pairwise interaction cover set size |B|: {size_B}")
        return size_B

if __name__ == "__main__":
    files_to_process = ["busybox.dimacs", "toybox.dimacs", "embtoolkit.dimacs", "uClinux.dimacs", "buildroot.dimacs"]
    script_dir = Path(__file__).resolve().parent
    base_dir = script_dir.parent / "resources" / "conf-dimacs"
    if not base_dir.is_dir():
        print(f"Error: Directory '{base_dir}' not found. Please ensure the DIMACS files are in this directory.", file=sys.stderr); sys.exit(1)

    all_results = {}
    for filename in files_to_process:
        file_path = base_dir / filename
        if not file_path.exists(): 
            print(f"Warning: File {file_path} not found, skipping.")
            continue
        print(f"\n{'='*20} Processing {filename} {'='*20}")
        try:
            analyzer = ConfigSystemAnalyzer(file_path)
            results = {
                'i_nodes': analyzer.report_i_bdd_nodes(),
                'ii_configs': analyzer.report_ii_valid_configurations(),
                'iii_ratio': analyzer.report_iii_urs_ratio(),
                'iv_interactions': analyzer.report_iv_pairwise_interactions(),
                'v_cover_size': analyzer.report_v_pairwise_cover_size()
            }
            all_results[filename] = results
            print(f"--- Finished processing {filename} ---")
        except Exception as e:
            print(f"\nA critical error occurred while processing {filename}: {e}", file=sys.stderr)
            import traceback; traceback.print_exc()

    print("\n" + "=" * 70)
    print(" " * 20 + "Final Summary Report (using OxiDD)")
    print("=" * 70)
    for filename, res in all_results.items():
        print(f"\n--- {filename} ---")
        
        ii_val = res.get('ii_configs', 'N/A')
        try:
            if isinstance(ii_val, (int, float)) and ii_val > 10**9: ii_str = f"{ii_val:.2e}"
            else: ii_str = f"{ii_val:,}" if isinstance(ii_val, (int, float)) else "N/A"
        except (OverflowError, TypeError):
             ii_str = "Too large to display"

        i_val = res.get('i_nodes', 'N/A')
        iii_val = res.get('iii_ratio', 'N/A')
        iv_val = res.get('iv_interactions', 'N/A')
        v_val = res.get('v_cover_size', 'N/A')
        
        print(f"  (i)   BDD Nodes:          {i_val:,}" if isinstance(i_val, int) else f"  (i)   BDD Nodes:          {i_val}")
        print(f"  (ii)  Valid Configs |V|:  {ii_str}")
        print(f"  (iii) x42 URS Ratio k1/k0:  {iii_val}")
        print(f"  (iv)  Pairwise Interactions: {iv_val:,}" if isinstance(iv_val, int) else f"  (iv)  Pairwise Interactions: {iv_val}")
        print(f"  (v)   Cover Set Size |B|:   {v_val:,}" if isinstance(v_val, int) else f"  (v)   Cover Set Size |B|:   {v_val}")
        
    print("=" * 70)
    print("All analyses complete.")
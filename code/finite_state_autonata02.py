#!/usr/bin/env python3
"""
Finite State Automata Reachability Analysis using BDDs
Compatible with OxiDD 0.10–0.12 (and likely newer)
Includes detailed debug output similar to dd.autoref version
Author: Adapted for TU/e 2IMF25 Assignment (Phoenix/Echoira)
"""

from oxidd.bdd import BDDManager


class BAFileParser:
    """Parser for BA (Büchi Automaton) file format"""

    @staticmethod
    def parse_ba_file(filename):
        with open(filename, 'r', encoding='utf-8') as f:
            content = f.read().strip()

        lines = content.split('\n')
        initial_state = None
        transitions = []
        all_states = set()
        state_id_map = {}
        next_state_id = 0

        for line in lines:
            line = line.strip()
            if not line:
                continue

            # First bracketed line is the initial state
            if line.startswith('[') and initial_state is None:
                initial_state = line
                state_id = BAFileParser._get_state_id(
                    state_id_map, initial_state, next_state_id)
                next_state_id += 1
                all_states.add(state_id)

            elif '->' in line:
                parts = line.split('->')
                if len(parts) == 2:
                    left_side, right_side = parts[0].strip(), parts[1].strip()
                    action = 0
                    src_state = left_side

                    if ',' in left_side:
                        comma_parts = left_side.split(',', 1)
                        if len(comma_parts) == 2 and comma_parts[0].strip() in ['0', '1']:
                            action = int(comma_parts[0].strip())
                            src_state = comma_parts[1].strip()

                    dst_state = right_side
                    src_id = BAFileParser._get_state_id(
                        state_id_map, src_state, next_state_id)
                    if src_id == next_state_id:
                        next_state_id += 1
                    all_states.add(src_id)

                    dst_id = BAFileParser._get_state_id(
                        state_id_map, dst_state, next_state_id)
                    if dst_id == next_state_id:
                        next_state_id += 1
                    all_states.add(dst_id)

                    transitions.append((src_id, action, dst_id))

        accepting_states = set(all_states)
        initial_state_id = state_id_map.get(initial_state, 0)
        states = sorted(all_states)

        print(f"Parsed: {len(states)} states, {len(transitions)} transitions")
        print(f"Initial state ID: {initial_state_id}")
        print(f"State ID range: {min(states)} to {max(states)}")

        return FSA(states, [initial_state_id], transitions, list(accepting_states))

    @staticmethod
    def _get_state_id(state_id_map, state_repr, next_id):
        if state_repr in state_id_map:
            return state_id_map[state_repr]
        state_id_map[state_repr] = next_id
        return next_id


class FSA:
    """Finite State Automaton representation"""
    def __init__(self, states, initial, transitions, accepting):
        self.states = states
        self.initial = initial
        self.transitions = transitions
        self.accepting = accepting


class BDDReachabilityAnalyzer:
    """BDD-based reachability analysis (OxiDD-compat, with rich debug)"""

    def __init__(self, fsa):
        self.fsa = fsa
        # Node/table sizes kept generous; tweak if memory constrained
        self.bdd = BDDManager(1 << 20, 1 << 18, 1)
        self.state_vars = []
        self.next_state_vars = []
        self.action_var = None
        self._setup_variables()


    def _get_bdd_size(self, bdd_obj):
        """Return a simple complexity estimate for a BDD (OxiDD placeholder)."""
        try:
            return len(str(bdd_obj))  # 用表达式长度近似复杂度
        except Exception:
            return 0



    def _varset(self, vars_):
        """Build a cube-like OR aggregation usable in .exist()."""
        s = self.bdd.false()
        for v in vars_:
            s = s | v
        return s

    def _encode_state(self, state_idx, vars_):
        expr = self.bdd.true()
        for i, var in enumerate(vars_):
            bit = (state_idx >> i) & 1
            expr = expr & (var if bit else ~var)
        return expr

    def _rename_y_to_x(self, func):
        """Logical y→x rename using XNOR constraints + ∃y elimination (compat)."""
        eq = self.bdd.true()
        for x, y in zip(self.state_vars, self.next_state_vars):
            eq = eq & ((x & y) | ((~x) & (~y)))  # XNOR
        combined = func & eq
        for y in self.next_state_vars:
            combined = combined.exist(y)
        return combined

    # --------------------------- Variable setup ---------------------------
    def _setup_variables(self):
        max_state = max(self.fsa.states)
        m = max(1, max_state.bit_length())

        print(f"State range: 0 to {max_state}, need {m} bits")

        # Allocate variables in interleaved order: x0, y0, x1, y1, ...
        self.state_vars = []
        self.next_state_vars = []

        for i in range(m):
            x = self.bdd.new_var()   # current-state bit
            y = self.bdd.new_var()   # next-state bit
            self.state_vars.append(x)
            self.next_state_vars.append(y)

        # Add the action variable (0/1 transition)
        self.action_var = self.bdd.new_var()

        pseudo_names = []
        for i in range(m):
            pseudo_names.append(f"x{i}")
            pseudo_names.append(f"y{i}")
        pseudo_names.append('a')

        print(f"Using {m} bits to encode {len(self.fsa.states)} states")
        print(f"Variables (interleaved): {pseudo_names}")


    # ------------------------ BDD builders & kernels ---------------------
    def build_transition_relation(self):
        transition_bdd = self.bdd.false()
        total = len(self.fsa.transitions)
        print(f"Building transition relation with {total} transitions...")

        for i, (src, action, dst) in enumerate(self.fsa.transitions):
            if i % 500 == 0:
                print(f"  Processing transition {i}/{len(self.fsa.transitions)}...")
            src_bdd = self._encode_state(src, self.state_vars)
            action_bdd = self.action_var if action else ~self.action_var
            dst_bdd = self._encode_state(dst, self.next_state_vars)
            transition_bdd = transition_bdd | (src_bdd & action_bdd & dst_bdd)

        print("Transition relation built")
        return transition_bdd

    def build_initial_states(self):
        initial_bdd = self.bdd.false()
        for state in self.fsa.initial:
            initial_bdd = initial_bdd | self._encode_state(state, self.state_vars)
        return initial_bdd

    def build_accepting_states(self):
        accepting_bdd = self.bdd.false()
        for state in self.fsa.accepting:
            accepting_bdd = accepting_bdd | self._encode_state(state, self.state_vars)
        return accepting_bdd

    def transitive_closure(self, initial, transition, max_iter=100):
        reachable = initial
        old_reachable = None
        iterations = 0

        print("Computing transitive closure...")

        while reachable != old_reachable and iterations < max_iter:
            old_reachable = reachable
            image = (reachable & transition).exist(
                self._varset(self.state_vars + [self.action_var])
            )
            next_states = self._rename_y_to_x(image)
            reachable = reachable | next_states
            iterations += 1

            if iterations % 10 == 0:
                size = self._get_bdd_size(reachable)
                #print(f"  Iteration {iterations}, BDD complexity: {size}")

        print(f"Transitive closure converged in {iterations} iterations")
        return reachable

    # ----------------------------- Analyses ------------------------------
    def analyze_zero_transitions(self, T, I, F):
        print("\n=== Analysis (i): Only 0-transitions ===")
        T_0 = T & (~self.action_var)
        t0_size = self._get_bdd_size(T_0)
        # print(f"T_0 BDD complexity: {t0_size}")

        R_0 = self.transitive_closure(I, T_0)
        reachable_accepting = R_0 & F
        is_reachable = reachable_accepting != self.bdd.false()

        #print(f"R_0 BDD complexity: {self._get_bdd_size(R_0)}")
        #print(f"Reachable accepting states BDD complexity: {self._get_bdd_size(reachable_accepting)}")
        print(f"Accepting states reachable via 0-transitions: {is_reachable}")
        return is_reachable, R_0

    def analyze_one_transitions(self, T, I, F):
        print("\n=== Analysis (ii): Only 1-transitions ===")
        T_1 = T & self.action_var
        t1_size = self._get_bdd_size(T_1)
        #print(f"T_1 BDD complexity: {t1_size}")

        R_1 = self.transitive_closure(I, T_1)
        reachable_accepting = R_1 & F
        is_reachable = reachable_accepting != self.bdd.false()

        #print(f"R_1 BDD complexity: {self._get_bdd_size(R_1)}")
        #print(f"Reachable accepting states BDD complexity: {self._get_bdd_size(reachable_accepting)}")
        #print(f"Accepting states reachable via 1-transitions: {is_reachable}")
        return is_reachable, R_1

    def analyze_alternating_transitions(self, T, I, F):
        print("\n=== Analysis (iii): Alternating 0-1-0... transitions ===")
        T_0 = T & (~self.action_var)
        T_1 = T & self.action_var

        S0, S1 = I, self.bdd.false()
        old_S0, old_S1 = None, None
        iterations = 0
        max_iter = 50

        print("Computing alternating reachability...")

        while (S0 != old_S0 or S1 != old_S1) and iterations < max_iter:
            old_S0, old_S1 = S0, S1

            S0_new = (S1 & T_0).exist(self._varset(self.state_vars + [self.action_var]))
            S0_new = self._rename_y_to_x(S0_new)

            S1_new = (S0 & T_1).exist(self._varset(self.state_vars + [self.action_var]))
            S1_new = self._rename_y_to_x(S1_new)

            S0 = S0 | S0_new
            S1 = S1 | S1_new
            iterations += 1

            # Per-iteration debug (optional heavy): print sizes
            if iterations % 5 == 0:
                print(
                    f"  Iter {iterations}, S0 size = {self._get_bdd_size(S0)}, S1 size = {self._get_bdd_size(S1)}"
                )

        reachable_0 = S0 & F
        reachable_1 = S1 & F
        is_reachable = (reachable_0 | reachable_1) != self.bdd.false()

        print(f"Accepting states reachable via alternating transitions: {is_reachable}")
        return is_reachable, (S0, S1)



    def analyze(self):
        print("Building BDD representations...")
        T = self.build_transition_relation()
        I = self.build_initial_states()
        F = self.build_accepting_states()

        print("\nStarting reachability analyses...")

        # === (i) Only 0-transitions ===
        print("\n=== Analysis (i): Only 0-transitions ===")
        T_0 = T & (~self.action_var)
        t0_size = self._get_bdd_size(T_0)
        #print(f"T_0 BDD complexity: {t0_size}")

        print("Computing transitive closure...")
        R_0 = self.transitive_closure(I, T_0)
        r0_size = self._get_bdd_size(R_0)
        reachable_accepting = R_0 & F
        ra0_size = self._get_bdd_size(reachable_accepting)
        is_reachable_0 = reachable_accepting != self.bdd.false()
        #print(f"R_0 BDD complexity: {r0_size}")
        #print(f"Reachable accepting states BDD complexity: {ra0_size}")
        print(f"Accepting states reachable via 0-transitions: {is_reachable_0}")

        # === (ii) Only 1-transitions ===
        print("\n=== Analysis (ii): Only 1-transitions ===")
        T_1 = T & self.action_var
        t1_size = self._get_bdd_size(T_1)
        #print(f"T_1 BDD complexity: {t1_size}")

        print("Computing transitive closure...")
        R_1 = self.transitive_closure(I, T_1)
        r1_size = self._get_bdd_size(R_1)
        reachable_accepting = R_1 & F
        ra1_size = self._get_bdd_size(reachable_accepting)
        is_reachable_1 = reachable_accepting != self.bdd.false()
        #print(f"R_1 BDD complexity: {r1_size}")
        #print(f"Reachable accepting states BDD complexity: {ra1_size}")
        print(f"Accepting states reachable via 1-transitions: {is_reachable_1}")

        # === (iii) Alternating transitions ===
        print("\n=== Analysis (iii): Alternating 0-1-0... transitions ===")
        T_0 = T & (~self.action_var)
        T_1 = T & self.action_var

        print("Computing alternating reachability...")
        S0, S1 = I, self.bdd.false()
        old_S0, old_S1 = None, None
        iterations = 0
        max_iter = 50

        while (S0 != old_S0 or S1 != old_S1) and iterations < max_iter:
            old_S0, old_S1 = S0, S1
            S0_new = (S1 & T_0).exist(self._varset(self.state_vars + [self.action_var]))
            S0_new = self._rename_y_to_x(S0_new)
            S1_new = (S0 & T_1).exist(self._varset(self.state_vars + [self.action_var]))
            S1_new = self._rename_y_to_x(S1_new)
            S0 = S0 | S0_new
            S1 = S1 | S1_new
            iterations += 1

        reachable_0 = S0 & F
        reachable_1 = S1 & F
        is_reachable_alt = (reachable_0 | reachable_1) != self.bdd.false()
        print(f"Accepting states reachable via alternating transitions: {is_reachable_alt}")



        print("\n[explicit cross-check]")
        xc = explicit_reachability_checks(self.fsa)
        print(f"[explicit] verdicts -> only0={xc['only0']}, only1={xc['only1']}, alt={xc['alt']}")


        # Return results in same structure as 01
        return {
            "zero_transitions": is_reachable_0,
            "one_transitions": is_reachable_1,
            "alternating_transitions": is_reachable_alt,
        }

# ----- explicit (non-BDD) cross-checks -----
def explicit_reachability_checks(fsa):
    from collections import deque, defaultdict

        # 建图：分别为 action=0 / action=1
    g0, g1 = defaultdict(list), defaultdict(list)
    for s, a, t in fsa.transitions:
        (g0 if a == 0 else g1)[s].append(t)

    initials = set(fsa.initial)
    accepting = set(fsa.accepting)

        # 统计一下 0/1 转移数，避免“看上去为 0”
    n0 = sum(len(v) for v in g0.values())
    n1 = sum(len(v) for v in g1.values())
    print(f"[explicit] #transitions: 0-edges={n0}, 1-edges={n1}")

        # ① 仅 0 转移
    q, vis0 = deque(initials), set(initials)
    while q:
        u = q.popleft()
        for v in g0.get(u, []):
            if v not in vis0:
                vis0.add(v); q.append(v)
    r0_ok = len(vis0 & accepting) > 0
    print(f"[explicit] only-0: reachable_states={len(vis0)}, accept_reachable={r0_ok}")

        # ② 仅 1 转移
    q, vis1 = deque(initials), set(initials)
    while q:
        u = q.popleft()
        for v in g1.get(u, []):
            if v not in vis1:
                vis1.add(v); q.append(v)
    r1_ok = len(vis1 & accepting) > 0
    print(f"[explicit] only-1: reachable_states={len(vis1)}, accept_reachable={r1_ok}")

        # ③ 交替 0-1-0…（按照你BDD版的逻辑，第一步是走“1”）
        # 状态带上 parity：0层=经过偶数步（下一步尝试 1），1层=经过奇数步（下一步尝试 0）
    q = deque([(s, 0) for s in initials])
    seen = set((s, 0) for s in initials)
    reach0, reach1 = set(initials), set()  # 分别对应 S0, S1
    while q:
        u, par = q.popleft()
        if par == 0:   # 下一步用 1-edge
            for v in g1.get(u, []):
                st = (v, 1)
                if st not in seen:
                    seen.add(st); q.append(st); reach1.add(v)
        else:          # 下一步用 0-edge
            for v in g0.get(u, []):
                st = (v, 0)
                if st not in seen:
                    seen.add(st); q.append(st); reach0.add(v)
    alt_ok = (len(reach0 & accepting) > 0) or (len(reach1 & accepting) > 0)
    print(f"[explicit] alternating: |S0|={len(reach0)}, |S1|={len(reach1)}, accept_reachable={alt_ok}")

    return {
        "only0": r0_ok,
        "only1": r1_ok,
        "alt": alt_ok,
        "counts": {"n0": n0, "n1": n1, "S0": len(reach0), "S1": len(reach1), "R0": len(vis0), "R1": len(vis1)},
        }




def main():
    print("Finite State Automata Reachability Analysis using OxiDD (Debug/Compat Version)")
    print("=" * 60)
    ba_file = input("Enter the path to the BA file: ").strip()

    try:
        print(f"Parsing BA file: {ba_file}")
        fsa = BAFileParser.parse_ba_file(ba_file)
        print(f"FSA: {len(fsa.states)} states, {len(fsa.transitions)} transitions")

        analyzer = BDDReachabilityAnalyzer(fsa)
        results = analyzer.analyze()

        print("\n" + "=" * 60)
        print("FINAL RESULTS:")
        print(f"Accepting states reachable via only 0-transitions: {results['zero_transitions']}")
        print(f"Accepting states reachable via only 1-transitions: {results['one_transitions']}")
        print(f"Accepting states reachable via alternating transitions: {results['alternating_transitions']}")

        # Optional: print size dict
        sizes = results.get('bdd_sizes', {})
        if sizes:
            print("\nBDD size snapshot (global node proxy):")
            for k, v in sizes.items():
                print(f"  {k}: {v}")

    except Exception as e:
        import traceback
        print(f"Error: {e}")
        traceback.print_exc()


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""
Finite State Automata Reachability Analysis using BDDs
Support for BA (Büchi Automaton) file format
"""

from dd import autoref as _bdd
import re


class BAFileParser:
    """Parser for BA (Büchi Automaton) file format"""

    @staticmethod
    def parse_ba_file(filename):
        """
        Parse BA file format
        Format example:
          [0|0 0|0][0 0 0][0 0 0]
          0,[0|0 0|0][0 0 0][0 0 0]->[1|0 0|0][1 0 0][0 0 0]
        """
        with open(filename, 'r') as f:
            content = f.read().strip()

        lines = content.split('\n')

        initial_state = None
        transitions = []
        accepting_states = set()
        all_states = set()
        state_id_map = {}
        next_state_id = 0

        for line in lines:
            line = line.strip()
            if not line:
                continue

            if line.startswith('[') and initial_state is None:
                initial_state = line
                state_id = BAFileParser._get_state_id(state_id_map, initial_state, next_state_id)
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

                    src_id = BAFileParser._get_state_id(state_id_map, src_state, next_state_id)
                    if src_id == next_state_id:
                        next_state_id += 1
                    all_states.add(src_id)

                    dst_id = BAFileParser._get_state_id(state_id_map, dst_state, next_state_id)
                    if dst_id == next_state_id:
                        next_state_id += 1
                    all_states.add(dst_id)

                    transitions.append((src_id, action, dst_id))

        accepting_states = set(all_states)
        initial_state_id = state_id_map.get(initial_state, 0)
        states = sorted(list(all_states))

        print(f"Parsed: {len(states)} states, {len(transitions)} transitions")
        print(f"Initial state ID: {initial_state_id}")
        print(f"State ID range: {min(states)} to {max(states)}")

        return FSA(states, [initial_state_id], transitions, list(accepting_states))

    @staticmethod
    def _get_state_id(state_id_map, state_repr, next_id):
        if state_repr in state_id_map:
            return state_id_map[state_repr]
        else:
            state_id_map[state_repr] = next_id
            return next_id


class FSA:
    """Finite State Automata"""

    def __init__(self, states, initial, transitions, accepting):
        self.states = states
        self.initial = initial
        self.transitions = transitions
        self.accepting = accepting


class BDDReachabilityAnalyzer:
    """BDD-based reachability analysis for FSA"""

    def __init__(self, fsa):
        self.fsa = fsa
        self.bdd = _bdd.BDD()
        self.state_vars = None
        self.action_var = None
        self.next_state_vars = None
        self._setup_variables()

    def _setup_variables(self):
        n = len(self.fsa.states)
        max_state = max(self.fsa.states)
        m = max(1, max_state.bit_length())

        print(f"State range: 0 to {max_state}, need {m} bits")

        self.state_vars = [f'x{i}' for i in range(m)]
        self.action_var = 'a'
        self.next_state_vars = [f'y{i}' for i in range(m)]

        all_vars = self.state_vars + [self.action_var] + self.next_state_vars
        for var in all_vars:
            self.bdd.add_var(var)

        print(f"Using {m} bits to encode {n} states")
        print(f"Variables: {all_vars}")

    def _get_bdd_size(self, bdd_func):
        try:
            count = 0
            for _ in self.bdd.pick_iter(bdd_func, care_vars=None):
                count += 1
                if count > 1000:
                    break
            return count
        except Exception:
            return -1

    def _encode_state(self, state_idx, vars):
        expr = self.bdd.true
        for i, var in enumerate(vars):
            bit = (state_idx >> i) & 1
            var_bdd = self.bdd.var(var) if bit else ~self.bdd.var(var)
            expr = expr & var_bdd
        return expr

    def build_transition_relation(self):
        transition_bdd = self.bdd.false
        print(f"Building transition relation with {len(self.fsa.transitions)} transitions...")

        for i, (src, action, dst) in enumerate(self.fsa.transitions):
            if i % 500 == 0:
                print(f"  Processing transition {i}/{len(self.fsa.transitions)}...")

            src_bdd = self._encode_state(src, self.state_vars)
            action_bdd = self.bdd.var(self.action_var) if action else ~self.bdd.var(self.action_var)
            dst_bdd = self._encode_state(dst, self.next_state_vars)
            transition_bdd |= src_bdd & action_bdd & dst_bdd

        print(f"Transition relation built")
        return transition_bdd

    def build_initial_states(self):
        initial_bdd = self.bdd.false
        for state in self.fsa.initial:
            initial_bdd |= self._encode_state(state, self.state_vars)
        return initial_bdd

    def build_accepting_states(self):
        accepting_bdd = self.bdd.false
        for state in self.fsa.accepting:
            accepting_bdd |= self._encode_state(state, self.state_vars)
        return accepting_bdd

    def _existential_quantification(self, bdd_func, variables):
        if not variables:
            return bdd_func
        return self.bdd.exist(variables, bdd_func)

    def transitive_closure(self, initial, transition, max_iter=100):
        reachable = initial
        old_reachable = None
        iterations = 0

        print("Computing transitive closure...")

        while reachable != old_reachable and iterations < max_iter:
            old_reachable = reachable
            image = reachable & transition
            vars_to_quantify = self.state_vars + [self.action_var]
            image = self._existential_quantification(image, vars_to_quantify)
            rename_map = {f'y{i}': f'x{i}' for i in range(len(self.state_vars))}
            next_states = self.bdd.let(rename_map, image)
            reachable |= next_states
            iterations += 1

            if iterations % 10 == 0:
                size = self._get_bdd_size(reachable)
                print(f"  Iteration {iterations}, BDD complexity: {size}")

        print(f"Transitive closure converged in {iterations} iterations")
        return reachable

    def analyze_zero_transitions(self, T, I, F):
        print("\n=== Analysis (i): Only 0-transitions ===")
        T_0 = T & (~self.bdd.var(self.action_var))
        t0_size = self._get_bdd_size(T_0)
        print(f"T_0 BDD complexity: {t0_size}")

        R_0 = self.transitive_closure(I, T_0)
        reachable_accepting = R_0 & F
        is_reachable = reachable_accepting != self.bdd.false

        print(f"R_0 BDD complexity: {self._get_bdd_size(R_0)}")
        print(f"Reachable accepting states BDD complexity: {self._get_bdd_size(reachable_accepting)}")
        print(f"Accepting states reachable via 0-transitions: {is_reachable}")

        return is_reachable, R_0

    def analyze_one_transitions(self, T, I, F):
        print("\n=== Analysis (ii): Only 1-transitions ===")
        T_1 = T & self.bdd.var(self.action_var)
        t1_size = self._get_bdd_size(T_1)
        print(f"T_1 BDD complexity: {t1_size}")

        R_1 = self.transitive_closure(I, T_1)
        reachable_accepting = R_1 & F
        is_reachable = reachable_accepting != self.bdd.false

        print(f"R_1 BDD complexity: {self._get_bdd_size(R_1)}")
        print(f"Reachable accepting states BDD complexity: {self._get_bdd_size(reachable_accepting)}")
        print(f"Accepting states reachable via 1-transitions: {is_reachable}")

        return is_reachable, R_1

    def _image(self, states, transition):
        image = states & transition
        vars_to_quantify = self.state_vars + [self.action_var]
        image = self._existential_quantification(image, vars_to_quantify)
        rename_map = {f'y{i}': f'x{i}' for i in range(len(self.state_vars))}
        return self.bdd.let(rename_map, image)

    def analyze_alternating_transitions(self, T, I, F):
        print("\n=== Analysis (iii): Alternating 0-1-0... transitions ===")
        T_0 = T & (~self.bdd.var(self.action_var))
        T_1 = T & self.bdd.var(self.action_var)

        S0, S1 = I, self.bdd.false
        old_S0, old_S1 = None, None
        iterations = 0
        max_iter = 50

        print("Computing alternating reachability...")

        while (S0 != old_S0 or S1 != old_S1) and iterations < max_iter:
            old_S0, old_S1 = S0, S1
            S0_new = self._image(S1, T_0)
            S1_new = self._image(S0, T_1)
            S0 |= S0_new
            S1 |= S1_new
            iterations += 1

        reachable_0 = S0 & F
        reachable_1 = S1 & F
        is_reachable = (reachable_0 != self.bdd.false) or (reachable_1 != self.bdd.false)

        print(f"Accepting states reachable via alternating transitions: {is_reachable}")
        return is_reachable, (S0, S1)

    def analyze(self):
        print("Building BDD representations...")
        T = self.build_transition_relation()
        I = self.build_initial_states()
        F = self.build_accepting_states()

        print("\nStarting reachability analyses...")
        result_zero, R_0 = self.analyze_zero_transitions(T, I, F)
        result_one, R_1 = self.analyze_one_transitions(T, I, F)
        result_alt, (S0, S1) = self.analyze_alternating_transitions(T, I, F)

        return {
            "zero_transitions": result_zero,
            "one_transitions": result_one,
            "alternating_transitions": result_alt,
            "bdd_sizes": {
                "T": self._get_bdd_size(T),
                "I": self._get_bdd_size(I),
                "F": self._get_bdd_size(F),
                "R_0": self._get_bdd_size(R_0),
                "R_1": self._get_bdd_size(R_1),
                "S0": self._get_bdd_size(S0),
                "S1": self._get_bdd_size(S1),
            },
        }


def main():
    print("Finite State Automata Reachability Analysis using BDDs")
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
    except Exception as e:
        import traceback
        print(f"Error: {e}")
        traceback.print_exc()


if __name__ == "__main__":
    main()

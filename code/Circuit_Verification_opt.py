import re
from dd.autoref import BDD
from functools import reduce
import time

def parse_bench(filename):
    inputs, outputs, gates = [], [], {}
    with open(filename) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line.startswith("INPUT("):
                inputs.append(re.findall(r'INPUT\((.*?)\)', line)[0])
            elif line.startswith("OUTPUT("):
                outputs.append(re.findall(r'OUTPUT\((.*?)\)', line)[0])
            else:
                m = re.match(r'(\w+)\s*=\s*(\w+)\((.*?)\)', line)
                if m:
                    gate_name, gate_type, gate_inputs = m.groups()
                    gates[gate_name] = (gate_type.upper(), [i.strip() for i in gate_inputs.split(',')])
    return inputs, outputs, gates

def apply_multi(bdd, op, nodes):
    return reduce(lambda x, y: bdd.apply(op, x, y), nodes)

def build_bdd(inputs, gates, bdd):
    node_bdd = {var: bdd.var(var) for var in inputs}
    cache = {}

    def get_node(name):
        if name in node_bdd:
            return node_bdd[name]
        if name in cache:
            return cache[name]

        gate_type, gate_inputs = gates[name]
        children = [get_node(i) for i in gate_inputs]

        if gate_type == "AND":
            result = apply_multi(bdd, 'and', children)
        elif gate_type == "OR":
            result = apply_multi(bdd, 'or', children)
        elif gate_type == "NOT":
            result = bdd.apply('not', children[0])
        elif gate_type == "NAND":
            result = bdd.apply('not', apply_multi(bdd, 'and', children))
        elif gate_type == "NOR":
            result = bdd.apply('not', apply_multi(bdd, 'or', children))
        elif gate_type == "XOR":
            result = bdd.apply('xor', *children)
        elif gate_type == "XNOR":
            result = bdd.apply('not', bdd.apply('xor', *children))
        else:
            raise ValueError(f"Unknown gate type: {gate_type}")

        cache[name] = result
        return result

    for gate_name in gates:
        node_bdd[gate_name] = get_node(gate_name)

    cache.clear()
    return node_bdd

def check_equivalence(file1, file2):
    inputs1, outputs1, gates1 = parse_bench(file1)
    inputs2, outputs2, gates2 = parse_bench(file2)

    if len(outputs1) != len(outputs2):
        return False

    all_vars = set(inputs1) | set(inputs2) | set(gates1.keys()) | set(gates2.keys())
    bdd = BDD()
    bdd.declare(*all_vars)

    nodes1 = build_bdd(inputs1, gates1, bdd)
    nodes2 = build_bdd(inputs2, gates2, bdd)

    equivalent = all(nodes1[o1] == nodes2[o2] for o1, o2 in zip(outputs1, outputs2))

    nodes1.clear()
    nodes2.clear()
    del bdd

    return equivalent


if __name__ == "__main__":
    start_time = time.time()
    file_original = "circuit_bench\\circuit05.bench"
    file_optimized = "circuit_bench\\circuit05_opt.bench"
    equivalent = check_equivalence(file_original, file_optimized)
    print(f"Circuits equivalent? {equivalent}")
    end_time = time.time()
    print(f"Elapsed time: {end_time - start_time:.6f} seconds")


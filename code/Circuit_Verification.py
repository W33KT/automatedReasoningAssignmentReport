import re
from dd.autoref import BDD

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
    from functools import reduce
    return reduce(lambda x, y: bdd.apply(op, x, y), nodes)

def build_bdd(inputs, gates, bdd):
    node_bdd = {var: bdd.var(var) for var in inputs}

    sorted_gates = []
    remaining = gates.copy()
    while remaining:
        for gate_name, (gate_type, gate_inputs) in list(remaining.items()):
            if all(i in node_bdd for i in gate_inputs):
                children = [node_bdd[i] for i in gate_inputs]
                if gate_type == "AND":
                    node_bdd[gate_name] = apply_multi(bdd, 'and', children)
                elif gate_type == "OR":
                    node_bdd[gate_name] = apply_multi(bdd, 'or', children)
                elif gate_type == "NOT":
                    node_bdd[gate_name] = bdd.apply('not', children[0])
                elif gate_type == "NAND":
                    node_bdd[gate_name] = bdd.apply('not', apply_multi(bdd, 'and', children))
                elif gate_type == "NOR":
                    node_bdd[gate_name] = bdd.apply('not', apply_multi(bdd, 'or', children))
                elif gate_type == "XOR":
                    node_bdd[gate_name] = bdd.apply('xor', *children)
                elif gate_type == "XNOR":
                    node_bdd[gate_name] = bdd.apply('not', bdd.apply('xor', *children))
                else:
                    raise ValueError(f"Unknown gate type: {gate_type}")
                sorted_gates.append(gate_name)
                del remaining[gate_name]
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


    return all(nodes1[o1] == nodes2[o2] for o1, o2 in zip(outputs1, outputs2))


if __name__ == "__main__":
    file_original = "circuit_bench\\circuit01.bench"
    file_optimized = "circuit_bench\\circuit01_opt.bench"
    equivalent = check_equivalence(file_original, file_optimized)
    print(f"Circuits equivalent? {equivalent}")


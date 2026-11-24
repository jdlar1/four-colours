"""Exact nonnegative signed-matching block counts, modulo colour and cap symmetry."""

from collections import Counter, defaultdict
from functools import cache
from itertools import permutations, product
from pathlib import Path
from math import lcm
import sys


def symmetries():
    # Terminal pairs (2i, 2i+1) border the same hexagon.
    return [
        tuple((d * i + k) % 10 for i in range(10))
        for d in (1, -1)
        for k in range(int(d < 0), 10, 2)
    ]


GROUP = symmetries()
NAMES = [str.maketrans("ABC", "".join(p)) for p in permutations("ABC")]
SWAP = str.maketrans("AB", "BA")


@cache
def row_key(w):
    return min(
        min(v, v.translate(SWAP)) for v in ("".join(w[i] for i in p) for p in GROUP)
    )


@cache
def match(points):
    if not points:
        return ((),)
    return tuple(
        ((points[0], points[j]),) + a + b
        for j in range(1, len(points), 2)
        for a in match(points[1:j])
        for b in match(points[j + 1 :])
    )


def equations(words):
    survivors = {w.translate(table) for w in words for table in NAMES}
    rows = {row_key(w): Counter() for w in survivors}
    blocks = {}
    n_live = 0
    for mask in range(1024):
        p = tuple(i for i in range(10) if mask >> i & 1)
        if len(p) % 2:
            continue
        for pairing in match(p):
            for signs in product(range(2), repeat=len(pairing)):
                if sum(signs) % 2:
                    continue
                block = []
                for flips in product(range(2), repeat=len(pairing)):
                    w = list("C" * 10)
                    for (i, j), s, f in zip(pairing, signs, flips):
                        w[i] = "AB"[f]
                        w[j] = "AB"[f ^ s]
                    w = "".join(w)
                    if w not in survivors:
                        break
                    block.append(w)
                else:
                    n_live += 1
                    # D5 acts on matchings, preserving whether endpoints agree.
                    key = min(
                        tuple(
                            sorted(
                                (min(g[i], g[j]), max(g[i], g[j]), s)
                                for (i, j), s in zip(pairing, signs)
                            )
                        )
                        for g in GROUP
                    )
                    index = blocks.setdefault(key, len(blocks))
                    for w in block:
                        # Only the representative labelled word contributes.
                        # Other words in its orbit give the identical equation.
                        if w in rows:
                            rows[w][index] += 1
    assert all(rows.values())
    groups = defaultdict(list)
    for w in sorted(rows):
        groups[min(row_key(w.translate(t)) for t in NAMES)].append(w)
    differences = {}
    for group in groups.values():
        for w in group[1:]:
            difference = rows[w].copy()
            difference.subtract(rows[group[0]])
            differences[w] = {j: a for j, a in difference.items() if a}
    print(
        "surviving signed matchings",
        n_live,
        "block orbits",
        len(blocks),
        "labelled word orbits",
        len(rows),
        "unlabelled word orbits",
        len(groups),
        flush=True,
    )
    return blocks, rows, differences


def solve(blocks, rows, differences):
    from z3 import Real, Solver, Sum, sat, unsat

    y = [Real(f"b{j}") for j in range(len(blocks))]
    solver = Solver()
    solver.add([v >= 0 for v in y])
    solver.add(Sum(y) >= 1)
    for row in differences.values():
        solver.add(Sum([a * y[j] for j, a in row.items()]) == 0)
    status = solver.check()
    if status != sat:
        raise ValueError(f"nonzero block-count feasibility: {status}")

    def coefficients():
        model = solver.model()
        return [model.eval(v, model_completion=True).as_fraction() for v in y]

    values = coefficients()
    for word, row in sorted(rows.items()):
        if any(values[j] for j in row):
            continue
        solver.push()
        solver.add(Sum([a * y[j] for j, a in row.items()]) >= 1)
        status = solver.check()
        if status == sat:
            # Nonnegative solutions add. This keeps the union of their supports.
            values = [a + b for a, b in zip(values, coefficients())]
        elif status == unsat:
            print("forced zero labelled orbit", word)
        else:
            raise ValueError(f"support check for {word}: {status}")
        solver.pop()
    denominator = lcm(*(v.denominator for v in values))
    return [int(v * denominator) for v in values]


if __name__ == "__main__":
    words = Path(sys.argv[1]).read_text().splitlines()
    blocks, rows, differences = equations(words)
    certificate = Path(__file__).with_name("block_weights.txt")
    if sys.argv[2:] == ["--solve"]:
        integers = solve(blocks, rows, differences)
        certificate.write_text(" ".join(map(str, integers)) + "\n")
    else:
        integers = list(map(int, certificate.read_text().split()))
    assert len(integers) == len(blocks) and min(integers) >= 0 and any(integers)
    assert all(
        sum(a * integers[j] for j, a in row.items()) == 0
        for row in differences.values()
    )
    positive = {w for w, row in rows.items() if any(integers[j] for j in row)}
    size = sum(any(row_key(w.translate(t)) in positive for t in NAMES) for w in words)
    print(
        "positive block orbits",
        sum(x > 0 for x in integers),
        "max coefficient",
        max(integers),
        "positive labelled word orbits",
        len(positive),
        "positive canonical boundary classes",
        size,
    )

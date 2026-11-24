"""Enumerate the RSST sparse contracts (conditions in sections 3.2 and 3.5)."""

from collections import Counter
from itertools import combinations
from pathlib import Path
import sys


def cap_faces():
    faces = []
    for i in range(5):
        a, b = 10 + i, 10 + (i + 1) % 5
        x, y, z = 2 * i, 2 * i + 1, (2 * i + 2) % 10
        faces.extend(((15, a, b), (a, b, z), (a, x, y), (a, y, z)))
    return faces


def test_contract(survivors):
    faces = cap_faces()
    edges = sorted({tuple(sorted(e)) for f in faces for e in combinations(f, 2)})
    candidates = [e for e in edges if max(e) >= 10]
    triangles = {
        e: {i for i, f in enumerate(faces) if set(e) <= set(f)} for e in candidates
    }
    neighbours = [
        {b if a == v else a for a, b in edges if v in (a, b)} for v in range(16)
    ]
    boundary = []
    for word in survivors:
        # Fix the name of boundary vertex 0 and integrate Tait differences.
        colours = [0]
        for c in word[:-1]:
            colours.append(colours[-1] ^ (ord(c) - 64))
        assert colours[-1] ^ (ord(word[-1]) - 64) == 0
        boundary.append(colours)

    def bad_word(contract):
        root = list(range(16))
        for u, v in contract:
            a, b = root[u], root[v]
            root = [a if x == b else x for x in root]
        adjacency = {a: set() for a in root}
        for u, v in edges:
            if (u, v) in contract:
                continue
            a, b = root[u], root[v]
            if a == b:
                raise ValueError("noncontracted loop in locally safe contract")
            adjacency[a].add(b)
            adjacency[b].add(a)
        fixed = set(root[:10])
        free = sorted(set(root) - fixed, key=lambda v: -len(adjacency[v] & fixed))
        seen = set()
        equal, unequal = [], []
        for v in range(10):
            a = root[v]
            if a in seen:
                equal.append((v, root.index(a)))
            else:
                for b in adjacency[a] & seen:
                    unequal.append((v, root.index(b)))
                seen.add(a)

        def extend(i):
            if i == len(free):
                return True
            v = free[i]
            available = {0, 1, 2, 3} - {assignment.get(w) for w in adjacency[v]}
            for c in available:
                assignment[v] = c
                if extend(i + 1):
                    return True
            assignment.pop(v, None)
            return False

        for colours in boundary:
            if any(colours[i] != colours[j] for i, j in equal):
                continue
            if any(colours[i] == colours[j] for i, j in unequal):
                continue
            assignment = dict(zip(root[:10], colours))
            if extend(0):
                return True
        return False

    for size in range(1, 5):
        stats = Counter()
        for contract in combinations(candidates, size):
            stats["all"] += 1
            if len(set.union(*(triangles[e] for e in contract))) != 2 * size:
                continue
            stats["sparse"] += 1
            ends = {x for e in contract for x in e}
            if size == 4 and not any(
                len(ends & neighbours[v]) >= 3
                and (v != 15 or not ends <= neighbours[v])
                for v in range(10, 16)
            ):
                continue
            stats["safe"] += 1
            if not bad_word(contract):
                stats["passing"] += 1
                print("passing contract", contract)
        print(size, dict(stats), flush=True)


if __name__ == "__main__":
    test_contract(Path(sys.argv[1]).read_text().splitlines())

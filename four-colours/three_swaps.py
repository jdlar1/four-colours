"""Check the explicit distance-three witness after removing the top pentagon."""

from collections import defaultdict
from check import moves, singletons


def ring(size, offset):
    return [(offset + i, offset + (i + 1) % size) for i in range(size)]


edges = (
    ring(10, 0)
    + ring(10, 10)
    + [(2*i + 1, 10 + 2*i) for i in range(5)]
    + ring(5, 20)
    + [(10 + 2*i + 1, 20 + i) for i in range(5)]
    + [(2*i, 25 + i) for i in range(5)]
)
witness = "ABACABABCB" + "BCABABABCA" + "CBCCA" + "BABAC" + "ACCCB" + "CCBCA"


def extendible(state):
    return singletons(state[-5:]) in [
        {i, (i + 1) % 5} for i in range(5)
    ]


def main():
    incident = defaultdict(list)
    for (u, v), c in zip(edges, witness, strict=True):
        incident[u].append(c)
        incident[v].append(c)
    assert all(sorted(incident[v]) == list("ABC") for v in range(25))

    first = set(moves(witness, edges))
    assert len(first) == 7 and not extendible(witness)
    assert not any(extendible(t) for t in first)
    assert not any(extendible(u) for t in first for u in moves(t, edges))

    current = witness
    for edge_index, palette in [(0, "AB"), (1, "AC"), (2, "AB")]:
        # An edge plus the palette identifies the component uniquely.
        current, = (s for s in moves(current, edges)
                    if {s[edge_index], current[edge_index]} == set(palette))
        print(palette, "on the component of rim edge", edge_index, "gives", current[-5:])
    assert extendible(current)


if __name__ == "__main__":
    main()

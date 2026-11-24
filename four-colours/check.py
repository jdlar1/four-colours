"""Check the pentagon claims and the nine-vertex example. Standard library only."""

from collections import Counter, deque
from itertools import combinations, product

COLOURS = "ABC"
PAIRS = tuple(combinations(COLOURS, 2))
PORTS = (0, 1, 2, 4, 6)
SPOKES = (3, 5, 7)
EDGES = (
    [(i, (i + 1) % 8) for i in range(8)]
    + [(8, i) for i in SPOKES]
    + [(9 + j, i) for j, i in enumerate(PORTS)]
)
WITNESS = "CBACBCBA" + "BAC" + "BACAA"


def proper_cycle(size):
    for word in product(COLOURS, repeat=size):
        if all(c != word[i - 1] for i, c in enumerate(word)):
            yield word


def third_at_rim(rim, i):
    return next(c for c in COLOURS if c not in (rim[i - 1], rim[i]))


def exterior_colourings():
    for rim in proper_cycle(8):
        spokes = [third_at_rim(rim, i) for i in SPOKES]
        if len(set(spokes)) == 3:
            ports = [third_at_rim(rim, i) for i in PORTS]
            yield "".join((*rim, *spokes, *ports))


def moves(state, edges=EDGES):
    for pair in PAIRS:
        remaining = {i for i, colour in enumerate(state) if colour in pair}
        while remaining:
            stack = [remaining.pop()]
            changed = list(state)
            while stack:
                i = stack.pop()
                changed[i] = pair[1] if state[i] == pair[0] else pair[0]
                neighbours = {j for j in remaining if set(edges[i]).intersection(edges[j])}
                remaining -= neighbours
                stack.extend(neighbours)
            yield "".join(changed)


def singletons(word):
    return frozenset(i for i, c in enumerate(word) if word.count(c) == 1)


def main():
    completions = Counter(
        "".join(third_at_rim(rim, i) for i in range(5)) for rim in proper_cycle(5)
    )
    adjacent = [frozenset((i, (i + 1) % 5)) for i in range(5)]
    diagonal = [frozenset((i, (i + 2) % 5)) for i in range(5)]
    for letters in product(COLOURS, repeat=5):
        word = "".join(letters)
        expected = sorted(Counter(word).values()) == [1, 1, 3] and singletons(word) in adjacent
        assert completions[word] == int(expected)

    states = set(exterior_colourings())
    assert WITNESS in states
    counts = Counter(singletons(s[-5:]) for s in states)
    a = [counts[p] for p in adjacent]
    b = [counts[p] for p in diagonal]
    assert len({a[i] - b[i] - b[i - 1] for i in range(5)}) == 1
    distances = {s: 0 for s in states if s[-5:] in completions}
    queue = deque(distances)
    while queue:
        state = queue.popleft()
        for other in moves(state):
            assert other in states
            if other not in distances:
                distances[other] = distances[state] + 1
                queue.append(other)
    assert distances.keys() == states
    assert distances[WITNESS] == 2
    by_distance = sorted(Counter(distances.values()).items())
    print(f"{len(completions)} extendible labelled boundary words, each with one completion")
    print(f"{len(states)} exterior colourings, counts by minimum swaps {by_distance}")
    print(f"Adjacent counts {a}, diagonal counts {b}")


if __name__ == "__main__":
    main()

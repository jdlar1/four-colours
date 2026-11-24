"""Exact Tait-colouring and Kempe-component check on the truncated icosahedron exterior."""

from collections import Counter, defaultdict, deque
from itertools import combinations
from pathlib import Path
import sys


def canon(word):
    names = dict(zip(dict.fromkeys(word), "ABC"))
    return "".join(names[x] for x in word)


def exterior():
    # The dual of the truncated icosahedron has a vertex for each original
    # vertex and each original triangular face. Adjacent face centres and
    # incident vertex/face centres are adjacent.
    faces = []
    upper = lambda i: 1 + i % 5
    lower = lambda i: 6 + i % 5
    for i in range(5):
        faces.extend(
            (
                (0, upper(i), upper(i + 1)),
                (upper(i), upper(i + 1), lower(i)),
                (upper(i + 1), lower(i), lower(i + 1)),
                (11, lower(i), lower(i + 1)),
            )
        )
    centres = defaultdict(list)
    for i, face in enumerate(faces):
        for a, b in combinations(sorted(face), 2):
            centres[a, b].append(12 + i)
    triangles = []
    removed = {0, *(12 + 4 * i for i in range(5))}
    for (a, b), (f, g) in centres.items():
        for v in (a, b):
            if not removed.intersection((v, f, g)):
                triangles.append((v, f, g))
    ring = [v for i in range(5) for v in (upper(i), 13 + 4 * i)]
    # Put the terminal edges first, in the gap convention of cap_probe.
    edge = lambda u, v: tuple(sorted((u, v)))
    terminals = [edge(v, ring[(i + 1) % 10]) for i, v in enumerate(ring)]
    internal = sorted(
        {edge(a, b) for f in triangles for a, b in combinations(f, 2)} - set(terminals)
    )
    edges = terminals + internal
    incident = [[] for _ in edges]
    for f in triangles:
        triple = [edges.index(edge(a, b)) for a, b in combinations(f, 2)]
        for e in triple:
            incident[e].append(triple)
    assert len(triangles) == 40 and len(edges) == 65
    assert list(map(len, incident)) == [1] * 10 + [2] * 55
    return edges, incident


def classify(remaining):
    edges, incident = exterior()
    adjacency = defaultdict(set)
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    order = []
    unseen = set(adjacency)
    while unseen:
        v = max(
            unseen, key=lambda u: (len(adjacency[u] - unseen), len(adjacency[u]), -u)
        )
        unseen.remove(v)
        order.append(v)
    earlier = {v: adjacency[v] & set(order[:i]) for i, v in enumerate(order)}
    colour = {}
    # Vertex naming up to S4 is equivalent to edge naming up to S3 because
    # all permutations of F2^2 are affine and the exterior disk is connected.
    states = set()
    by_word = Counter()

    def visit(i, names):
        if i == len(order):
            word = canon([colour[u] ^ colour[v] for u, v in edges[:10]])
            by_word[word] += 1
            if word in remaining:
                masks = [0] * 3
                for j, (u, v) in enumerate(edges):
                    masks[(colour[u] ^ colour[v]) - 1] |= 1 << j
                states.add(tuple(sorted(masks)))
            return
        v = order[i]
        forbidden = {colour[u] for u in earlier[v]}
        for c in range(min(4, names + 1)):
            if c not in forbidden:
                colour[v] = c
                visit(i + 1, max(c + 1, names))

    visit(0, 0)
    print(
        "exterior orbits",
        sum(by_word.values()),
        "boundary classes",
        len(by_word),
        "survivor classes",
        len(by_word.keys() & remaining),
        "survivor orbits",
        len(states),
        flush=True,
    )
    assert len(states) == sum(by_word[w] for w in remaining)
    # Single components include closed interior cycles. The mask adjacency
    # gives the line graph of the cubic exterior including terminal edges.
    touches = [
        sum(1 << j for j in {j for face in faces for j in face if j != i})
        for i, faces in enumerate(incident)
    ]

    def neighbours(s):
        for a, b in combinations(range(3), 2):
            active = s[a] | s[b]
            while active:
                todo = active & -active
                component = 0
                while todo:
                    bit = todo & -todo
                    todo ^= bit
                    component |= bit
                    todo |= touches[bit.bit_length() - 1] & active & ~component
                active ^= component
                t = list(s)
                t[a] ^= component
                t[b] ^= component
                yield tuple(sorted(t))

    # A closed subset exists iff an entire connected component is trapped.
    # Explore components of the graph induced by bad states, testing exits.
    visited = set()
    trapped = 0
    regions = 0
    for state in states:
        if state in visited:
            continue
        regions += 1
        seen = 0
        exits = False
        queue = deque([state])
        visited.add(state)
        while queue:
            s = queue.popleft()
            seen += 1
            for t in neighbours(s):
                if t not in states:
                    exits = True
                elif t not in visited:
                    visited.add(t)
                    queue.append(t)
        if not exits:
            trapped += seen
    print(
        "bad-induced regions",
        regions,
        "orbits in survivor-only Kempe components",
        trapped,
    )


if __name__ == "__main__":
    classify({canon(w) for w in Path(sys.argv[1]).read_text().splitlines()})

"""Finite boundary certificates for a pentagon and its five neighbouring faces."""

from collections import Counter
from functools import lru_cache
from itertools import combinations, product

COLOURS = "ABC"


@lru_cache(maxsize=None)
def canonical(word):
    """Forget colour names while keeping the terminal order."""
    names = dict(zip(dict.fromkeys(word), COLOURS))
    return "".join(names[c] for c in word)


def rim_words(size, prefix=""):
    if len(prefix) == size:
        if prefix[-1] != prefix[0]:
            yield prefix
        return
    for colour in COLOURS:
        if not prefix or prefix[-1] != colour:
            yield from rim_words(size, prefix + colour)


def cap_completions(gaps):
    """Count interior colourings for each labelled outer boundary word."""
    size = sum(gaps)
    inward = {sum(gaps[:i]) for i in range(5)}
    counts = Counter()
    third = {(a, b): c for a in COLOURS for b in COLOURS for c in COLOURS
             if len({a, b, c}) == 3}
    for rim in rim_words(size):
        spokes = [third[rim[i - 1], rim[i]] for i in range(size)]
        inner = [spokes[i] for i in range(size) if i in inward]
        singles = [i for i, c in enumerate(inner) if inner.count(c) == 1]
        if len(singles) == 2 and (singles[0] - singles[1]) % 5 in (1, 4):
            outer = "".join(spokes[i] for i in range(size) if i not in inward)
            counts[outer] += 1
    return counts


@lru_cache(maxsize=None)
def noncrossing(terminals):
    if not terminals:
        return ((),)
    result = []
    for j in range(1, len(terminals), 2):
        for inside in noncrossing(terminals[1:j]):
            for outside in noncrossing(terminals[j + 1:]):
                result.append(((terminals[0], terminals[j]),) + inside + outside)
    return tuple(result)


def palette_options(word, pair, ids):
    """For each possible pairing, list the states reachable by disjoint swaps."""
    a, b = pair
    active = tuple(i for i, c in enumerate(word) if c in pair)
    flipped = word.translate(str.maketrans(a + b, b + a))
    target_ids = {}
    options = []
    for matching in noncrossing(active):
        masks = [0]
        # Complementary subsets differ only by globally renaming a and b.
        for i, j in matching[:-1]:
            path = (1 << i) | (1 << j)
            masks.extend([mask | path for mask in masks])
        for mask in masks[1:]:
            if mask not in target_ids:
                target = "".join(flipped[i] if mask & (1 << i) else c
                                 for i, c in enumerate(word))
                target_ids[mask] = ids[canonical(target)]
        options.append(tuple(target_ids[m] for m in masks[1:]))
    return options


def certify(gaps):
    counts = cap_completions(gaps)
    if gaps == (2,) * 5:
        assert len(counts) == 60 and set(counts.values()) == {2}

    size = sum(gaps) - 5
    words = [w for w in map("".join, product(COLOURS, repeat=size))
             if all(w.count(c) % 2 == size % 2 for c in COLOURS) and canonical(w) == w]
    ids = {w: i for i, w in enumerate(words)}
    direct = {ids[canonical(w)] for w in counts}
    remaining = set(ids.values()) - direct
    options = {
        i: [palette_options(words[i], pair, ids) for pair in combinations(COLOURS, 2)]
        for i in remaining
    }
    rounds = [len(direct)]
    while remaining:
        # Choose a palette. For EVERY planar matching there must be SOME
        # path subset reaching a word certified in a strictly earlier round.
        new = {i for i in remaining if any(
            all(any(target not in remaining for target in subset_targets)
                for subset_targets in matching_targets)
            for matching_targets in options[i]
        )}
        if not new:
            break
        rounds.append(len(new))
        remaining -= new
    return rounds, len(remaining)


def main():
    # All cyclic arrangements up to rotation and reflection.
    for pattern in ("22222", "32222", "33222", "32322", "33322", "33232", "33332", "33333"):
        rounds, remaining = certify(tuple(map(int, pattern)))
        print(pattern, "newly certified per round", rounds, "unresolved", remaining)
        assert remaining == (1220 if pattern == "33333" else 0)


if __name__ == "__main__":
    main()

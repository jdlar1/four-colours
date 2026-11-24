"""Independent exhaustive decagon reducer check using the original caps.py."""

from collections import Counter
from itertools import combinations, product
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import caps


def check():
    colours = caps.COLOURS
    direct = {caps.canonical(w) for w in caps.cap_completions((3,) * 5)}
    cycle_words = Counter()
    for rim in caps.rim_words(10):
        spokes = "".join(
            next(c for c in colours if c not in (rim[i - 1], rim[i])) for i in range(10)
        )
        cycle_words[caps.canonical(spokes)] += 1
    words = [
        "".join(w)
        for w in product(colours, repeat=10)
        if all(w.count(c) % 2 == 0 for c in colours)
    ]
    ids = {w: i for i, w in enumerate(sorted({caps.canonical(w) for w in words}))}
    remaining = {i for w, i in ids.items() if w not in direct}
    options = {
        i: [caps.palette_options(w, p, ids) for p in combinations(colours, 2)]
        for w, i in ids.items()
        if i in remaining
    }
    wheel = {ids[w] for w in cycle_words}
    hits = [len(wheel - remaining)]
    while True:
        new = {
            i
            for i in remaining
            if any(
                all(any(t not in remaining for t in targets) for targets in palette)
                for palette in options[i]
            )
        }
        if not new:
            break
        hits.append(len(wheel & new))
        remaining -= new
    print("classes", len(ids), "direct", len(direct), "survivors", len(remaining))
    print(
        "cycle assignments",
        sum(cycle_words.values()),
        "cycle classes",
        len(wheel),
        "cycle hits per round",
        hits,
        "cycle survivor intersection",
        len(wheel & remaining),
    )
    assert len(ids) == 2461 and len(remaining) == 1220 and not wheel & remaining
    if len(sys.argv) == 2:
        native = {caps.canonical(w) for w in Path(sys.argv[1]).read_text().splitlines()}
        assert native == {w for w, i in ids.items() if i in remaining}
        print("native survivor set agrees word for word")


if __name__ == "__main__":
    check()

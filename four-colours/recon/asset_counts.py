"""Read RSST or Steinberger free completions and tabulate their headers."""

from collections import Counter
import re
from pathlib import Path
import sys


def report(filename):
    counters = {
        k: Counter() for k in ("ring", "vertices", "interior", "contract", "ring/type")
    }
    blocks = re.split(r"\n\s*\n", Path(filename).read_text().strip())
    for block in blocks:
        fields = block.splitlines()
        n, r, _, left = map(int, fields[1].split())
        contract = list(map(int, fields[2].split()))
        assert len(contract) == 1 + 2 * contract[0]
        assert (left > 0) == (contract[0] > 0)
        for i, row in enumerate(fields[3 : 3 + n], 1):
            vertex, degree, *adjacent = map(int, row.split())
            assert vertex == i and len(adjacent) == degree
        assert len(" ".join(fields[3 + n :]).split()) == n
        for kind, value in zip(
            counters, (r, n, n - r, contract[0], (r, "C" if left else "D"))
        ):
            counters[kind][value] += 1
    print(filename, len(blocks))
    for key, counts in counters.items():
        print(key, dict(sorted(counts.items())))


if __name__ == "__main__":
    for path in sys.argv[1:]:
        report(path)

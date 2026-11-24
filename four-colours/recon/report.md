# The five-hexagon cap is C-reducible

The embedded `33333` cap cannot occur in a smallest bridgeless planar cubic counterexample. Replace its 20 vertices by a 10-cycle, retaining the terminals in order. Every colouring of the replacement gives an exterior colouring that the existing Kempe argument can repair. The RSST verifier independently accepts a four-edge contract for the same configuration. [RSST-format certificate](33333.conf)

## The decagon reducer

The D check starts with 2,461 boundary classes modulo global colour names. Exactly 530 extend across the cap. Successive Kempe rounds certify 305, 40, 30, 15, 31, 55, 40, 65, 40, 15, 25, 15, 20, 5 and 10 more. The fixed point has 1,220 survivors. The C++ signed-matching program and the original Python pairing algorithm agree on every surviving word. [Native probe](cap_probe.cpp) · [Python cross-check](wheel_check.py)

The replacement cycle has 1,026 proper labelled rim assignments and 171 canonical terminal words. Of those words, 25 extend directly and the other 146 enter the certified set by round 13. **The cycle admits zero survivors.** In the dual this is a decagon with one new vertex adjacent to its ten boundary vertices.

The replacement fits in the original disk and keeps terminal order. Every new cycle edge lies on the decagon. For a retained edge, its old alternate path can reroute each excursion into the cap through the connected replacement. This proves bridgelessness after gluing, even if the exterior has several components. Minimality therefore supplies a colouring of the smaller graph. Its restriction to the exterior has a certified boundary word, and each certified word admits a sequence of exterior swaps followed by a cap completion.

## Exhaustive reducer searches

A separate search generated every embedded simple triangulation of a decagon with zero through five interior vertices. The original dual cap has six. For each candidate, the checker enumerates proper four-colourings, computes the XOR differences on consecutive ring vertices, and rejects an alignment as soon as it finds a surviving word. Global vertex colour permutations preserve the test. The cap's pentagonal rotations and reflections leave two boundary alignments to test. A passing disk has at least one alignment with zero overlap. The plantri counts identify embeddings up to isomorphism, including reflection. [Disk checker](disk_probe.cpp) · [Brinkmann and McKay's plantri distribution](https://users.cecs.anu.edu.au/~bdm/plantri/)

| Interior vertices | Generated disks | Passing disks |
|---:|---:|---:|
| 0 | 82 | 0 |
| 1 | 1,004 | 1 |
| 2 | 9,876 | 1 |
| 3 | 87,980 | 7 |
| 4 | 755,468 | 30 |
| 5 | 6,370,375 | 198 |
| **Total** | **7,224,785** | **237** |

The wheel is the unique minimum-size passing simple disk. The table tests the boundary criterion. The gluing proof above establishes safety for the wheel.

The strict RSST search considers subsets of the 25 non-ring edges in the cap's free completion. Sparsity allows at most one chosen edge in each triangular face. Sets of size four also require a triad. The checker contracts each eligible subset and tests extension of every survivor until it finds an overlap or exhausts the list. [Contract enumeration](contracts.py) · [RSST, sections 2 and 3](https://thomas.math.gatech.edu/PAP/fc.pdf)

| Contract size | Subsets | Sparse | Pass RSST structural checks | Zero survivor overlap |
|---:|---:|---:|---:|---:|
| 1 | 25 | 25 | 25 | 0 |
| 2 | 300 | 260 | 260 | 0 |
| 3 | 2,300 | 1,465 | 1,465 | 0 |
| 4 | 12,650 | 4,880 | 4,875 | 5 |

The five successful contracts are rotations. With ring vertices 1 through 10, peripheral interior vertices 11 through 15, and centre 16, one contract consists of **2–11, 12–13, 13–14 and 14–15**. The centre supplies the triad. It sees five contract endpoints among its neighbours, and the edge 2–11 does not face it. Stock `reduce.c` independently confirms the contract after obtaining 530 direct classes and 1,220 survivors. Its initial figure of 9,842 counts all ring edge words modulo colour names, before the parity filter used here. [Verifier input](33333.conf) · [Archived verifier](rsst/reduce.c)

## Planar realization and block counts

Excising the cap around one pentagon of the truncated icosahedron leaves a cubic exterior with 40 vertices, 55 internal edges and ten terminals. Its 10,710 exterior colouring orbits realize 1,981 canonical boundary words. Of these, **4,460 orbits realize 935 distinct survivors**. The checker traces every two-colour component, including closed interior cycles. The subgraph induced by the 4,460 orbits has 11 connected components. Each has a swap into a certified word. Thus **zero** of the fullerene exterior colourings belong to a Kempe component trapped within the survivors. The existence of a trapped component on a different planar exterior remains unresolved here. [Fullerene construction and checker](fullerene.py)

The signed-matching block-count equations alone admit a nonzero solution. For a fixed pair of colours, a matching and its endpoint signs specify a block. Swapping any subset of paths gives a bijection between colourings of the words in that block. Each word's count therefore equals the sum of the nonnegative weights of all compatible blocks. The three palette sums must agree after colour renaming. [Dvořák and Lidický, equation (2)](https://lidicky.name/pub/4cone-conj.pdf)

There are 1,585 surviving signed matchings. The cap symmetries give 177 matching orbits. Averaging any feasible count vector over these symmetries preserves nonnegativity and the equations, so the symmetric system detects feasibility. The stored integer certificate has 121 positive orbit weights, each at most three. It gives positive counts on **1,215 of the 1,220 survivors**. Exact rational feasibility checks force the other five counts to zero. Thus block counts exclude five more classes and leave a nonempty compatible support. Realizing that abstract support by a single planar exterior is a stronger condition. [Equation builder and certificate checker](block_counts.py) · [Integer weights](block_weights.txt)

## Compute budget on this host

The Ryzen 7 7840HS has eight physical cores and 16 logical CPUs. The native D engine uses one thread per configuration. It enumerates labelled ternary words, groups them under colour permutations, generates signed noncrossing matchings, and removes unsupported classes to a fixed point. The probes at rings 11 through 14 use larger gaps in the same five-spoke construction. A gap of four gives a seven-sided neighbouring face.

| Ring | Gaps | Canonical classes | Direct | Subsequent rounds | Survivors |
|---:|---|---:|---:|---:|---:|
| 10 | 33333 | 2,461 | 530 | 15 | 1,220 |
| 11 | 43333 | 7,381 | 1,128 | 6 | 5,488 |
| 12 | 43343 | 22,144 | 2,332 | 6 | 19,058 |
| 13 | 44433 | 66,430 | 4,716 | 4 | 60,021 |
| 14 | 44443 | 199,291 | 9,580 | 4 | 187,363 |

The stock RSST program reproduced the direct and final survivor counts at rings 12 and 14. These two runs stopped after reporting the survivors because their diagnostic inputs had empty contracts.

| Ring | Median process wall time | Seven-run range | Median engine time | Peak RSS, median [min, max] KiB | 16-worker throughput, jobs/s |
|---:|---:|---:|---:|---:|---:|
| 10 | 3.197497 ms | 3.096008–3.388502 ms | 1.842820 ms | 4,412 [4,364, 4,484] | 2,607.9 |
| 12 | 23.127531 ms | 22.365827–23.744366 ms | 21.646500 ms | 10,448 [10,444, 10,516] | 354.3 |
| 14 | 345.580403 ms | 344.373572–351.138943 ms | 343.981000 ms | 155,112 [155,084, 155,208] | 20.4 |

Serial timings include process launch, enumeration, all fixed-point rounds, result output and exit. Each case ran seven times in rotating order, pinned to logical CPU 2, with GCC 15.2.0, C++20, `-O3 -march=native`, Linux 7.0.0-43-generic. Linux `VmHWM` measures the executable's peak resident set. A separate profile of ring 14 put approximately one third of samples in word setup and one third in matching generation. Median process CPU time was 344.97 ms for that case. The host also ran other work during measurement. [Benchmark runner](benchmark.py) · [Individual measurements](benchmark.tsv)

For throughput, 16 workers each launched fresh single-threaded processes. Each batch comprised 64 copies of one cap, with five batches per size in rotating order. Median batch times were 0.024540514, 0.180639665 and 3.136600315 seconds for rings 10, 12 and 14. Ring 14 ranged from 3.051148075 to 3.150606160 seconds per batch. All 960 concurrent-run outputs and all 21 serial outputs matched their expected counts. Sixteen times the largest observed ring-14 worker peak is 2.37 GiB, an upper bound on the sum of these process peaks for such a batch. The budget applies to the selected cap geometries and direct sets. [Batch measurements](batch.tsv)

## Reproduce

Run from `four-colours/recon/` on Linux. All Python certificate checks below use the standard library. Optional regeneration of the block weights uses `z3-solver` with `block_counts.py /tmp/33333.words --solve`.

```sh
g++ -std=c++20 -O3 -march=native cap_probe.cpp -o /tmp/cap_probe
/tmp/cap_probe 33333 /tmp/33333.words
python3 wheel_check.py /tmp/33333.words
python3 contracts.py /tmp/33333.words
python3 fullerene.py /tmp/33333.words
python3 block_counts.py /tmp/33333.words
gcc -std=gnu89 -O2 -w rsst/reduce.c -o /tmp/rsst-reduce
/tmp/rsst-reduce 33333.conf
taskset -c 2 python3 benchmark.py /tmp/cap_probe
python3 benchmark.py /tmp/cap_probe --batch
```

The disk census used plantri 5.5 with outer chords and degree-two boundary vertices allowed. The source archive has SHA-256 `911cdf5bcca7294eb80f8f79fefc148183f7ba81da15b3aa4d6d2401a3bc7ded`. [plantri 5.5 source archive](https://users.cecs.anu.edu.au/~bdm/plantri/plantri55.tar.gz)

```sh
curl -fsSL https://users.cecs.anu.edu.au/~bdm/plantri/plantri55.tar.gz -o /tmp/plantri55.tar.gz
tar -xf /tmp/plantri55.tar.gz -C /tmp
cc -O3 /tmp/plantri55/plantri.c -o /tmp/plantri55-bin
g++ -std=c++20 -O3 -march=native disk_probe.cpp -o /tmp/disk_probe
set -o pipefail
for n in 10 11 12 13 14 15; do
    /tmp/plantri55-bin -P10c2m2 "$n" | /tmp/disk_probe /tmp/33333.words || exit 1
done
```

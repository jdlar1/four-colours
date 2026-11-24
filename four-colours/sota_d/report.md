# Verified purely D-reducible four-colour certificates

**2,484 configurations, with 91 at ring 16.** The minimum-count bundle removes 338 configurations (11.98%) from Steinberger’s 2,822 benchmark. It retains 2,024 original records, replaces 798 original records and adds 460 configurations. Every record passed the archived reducibility checker with an empty contract and zero surviving consistent classes. All eight presentations passed the unmodified archived discharging checker. [Minimum-count bundle](best_bundle/) · [Proof-file hashes and per-run totals](best_bundle/manifest.json)

| Certificate | Total | Ring 16 | Rule file |
|---|---:|---:|---|
| Published baseline | 2,822 | 161 | `L_42` |
| Fixed-rule minimum found | 2,636 | 127 | `L_42` |
| Minimum total found | **2,484** | **91** | `L_42` with 22 additional reflected rule pairs |
| Fixed-rule ring-first search | 2,828 | 82 | `L_42` |
| Refined-rule ring-first search | 2,826 | **75** | Same refined rules as the minimum-total bundle |

All four experimental certificates in this table passed the full gate. The rule file for the refined searches has 131 encoded entries, including reflections, versus 87 for the original 42 rules. The added entries transfer charge only between vertices of exact degree 7 or 8. The ring-first searches eliminated **79** and **86** of the original ring-16 configurations, respectively, with zero new ring-16 configurations. Maximum ring 15 and fewer than 2,200 total configurations remain open targets. [Fixed-rule minimum](broader/) · [Fixed-rule ring-first certificate](ringstress/) · [Refined ring-first certificate](ring_stress_bundle/)

| Ring | Published | Fixed-rule minimum | Minimum total | Refined ring-first |
|---:|---:|---:|---:|---:|
| 6 | 1 | 1 | 1 | 1 |
| 7 | 1 | 1 | 1 | 1 |
| 8 | 5 | 5 | 5 | 5 |
| 9 | 15 | 15 | 15 | 15 |
| 10 | 58 | 57 | 58 | 58 |
| 11 | 184 | 185 | 178 | 184 |
| 12 | 473 | 456 | 441 | 476 |
| 13 | 740 | 730 | 686 | 754 |
| 14 | 745 | 685 | 660 | 774 |
| 15 | 439 | 374 | 348 | 483 |
| 16 | 161 | 127 | 91 | 75 |
| **Total** | **2,822** | **2,636** | **2,484** | **2,826** |

## Verification

Run from `four-colours/sota_d`. The proof inputs are the configuration file, the rule file and eight presentations. The search programs are unnecessary for replay. The verification harness uses GCC, Python 3 and NetworkX. A fresh checkout can prepare the Python environment with `python3 -m venv .venv && .venv/bin/pip install networkx`. Repeating the optional MILP and lower-bound calculations also requires NumPy and SciPy.

```sh
export OMP_NUM_THREADS=8 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
sh verify.sh best_bundle 8
```

To replay the other certificates, use `sh verify.sh broader 8`, `sh verify.sh ringstress 8`, or `sh verify.sh ring_stress_bundle 8`. Direct sequential C replay from this directory uses the following commands.

```sh
set -eu
sh build.sh
./reduce best_bundle/unavoidable.conf > reduce-replay.log
for d in 5 6 7 8 9 10 11 12; do
    ./discharge "best_bundle/p$d" best_bundle/unavoidable.conf best_bundle/rules || exit 1
done
```

The verification harness additionally checks each success message, counts one D-reducible verdict per input record and checks zero contract length and zero declared exterior in every header. The parallel replay partitions the input by record position modulo the worker count. Each presentation runs in a separate directory because the author’s program writes `outlet.et`. The abstract isomorphism test distinguishes boundary vertices and uses degree-neighbourhood signatures followed by exact NetworkX graph matching. Abstract nonisomorphism also rules out embedded duplicates.

The source was downloaded from the author’s arXiv v3 archive. The archived C sources and seven presentations are under `steinberger/`. The configuration file SHA-256 is `61768599e85a45ff9bc884de06918d99c2c08cf68a6ad1048edd5d5f6f83c74d`. `check_archive.py` compares each extracted file against its archive member. `build.sh` compiles the original discharging source directly. It changes the matching-depth arrays to nine entries, the interval arrays to eighteen, and completes the diagnostic table for rings 15 and 16 in a separate reducibility build. [Steinberger’s source archive](https://arxiv.org/src/0905.0043v3) · [Paper](https://arxiv.org/abs/0905.0043)

### Degrees above 12

The executable reads hub degrees up to 12. The added degree-12 presentation checks twelve individual directed-edge bounds of 5 in units of one tenth. The high-degree extension uses their locality. The emitted degree-12 outlets and the interior images actually used by the verifier fit within spoke offsets −2 through +2 of the tested edge. No image uses the hub. The independent support audit `lift.py` measures those offsets on a logging copy, after a separate run of the archived executable has accepted the presentation.

For any larger degree, insert the extra spokes across the opposite cut, between offsets +5 and −6 of the 12-wheel. The directed triangles, fans, degree inequalities and cyclic neighbour order in the tested sector are preserved. The rule decoder excludes every outgoing rule for these hubs, and an incoming rule admitting 12 admits all larger degrees by the infinity convention. The per-edge proof uses the same positioned outlets and reducibility images on this sector. Thus the scaled final charge is at most `10(6−d)+5d = 60−5d ≤ 0`. The added transfers in the refined-rule experiments all have both endpoints of exact degree 7 or 8. Steinberger’s original separate large-degree argument also remains available when those are the only changes and its configurations are retained. [Steinberger, §4](https://arxiv.org/abs/0905.0043)

## Search

The baseline replay verified all 2,822 D-reducible records and degrees 5 through 12. The tracing fork records the inclusive degree interval of every cartwheel position, the presentation line, the reducibility call and the first embedding. A separate shared-prefix matcher enumerates the embedding questions for the entire library. On the original seven presentations it examined 1,765,728 stack states. The degree-12 certificate adds 660.

The baseline had 52 configurations uniquely matched on exactly one line, 124 on at most two, 339 on at most five and 674 on at most ten. There were 1,275 whose unique matches occurred exclusively on hubcap lines. The exact rare states are in `tail_axles.tsv.gz`, with columns for the one-based configuration ID, hub degree, presentation line, reduction call and the inclusive low/high interval for positions 0 through 5d.

| Degree | States needing a ring-16 match | Distinct presentation lines |
|---|---:|---:|
| 7 | 4,155 | 2,748 |
| 8 | 655 | 448 |
| 9 | 128 | 54 |
| 10 | 2 | 1 |
| Other tested degrees | 0 | 0 |

The fixed-rule search started with the original library and the purely D-reducible entries of the neighbouring project’s extended pool. Canonical deduplication left 15,014 candidates. The exact minimum of the first conservative frozen-trace model was 2,822. Lower counts became possible after changing the proofs on individual leaves. The local proof search tests symmetry and reducibility, computes pairwise upper bounds, finds a minimum-weight permutation for the hubcap double cover, and branches on degree inequalities when necessary. Every accepted change is serialized in the original presentation language.

Starting with 15,014 deduplicated records, three harvesting passes added 2,784, 1,505 and 359 D-reducible candidates to reach a 19,662-record library. The harvesting pass extracted triangulated disk interiors from sparse private axles across the eight hubs. It screened graph shapes against multiple baseline configurations, tested their free completions with the D-only reducer, and discarded positive surviving consistent sets. A second pass ranked disks and two-block configurations against concrete positive-charge wheels. The OpenMP driver caps its own thread count at eight.

The integer set-cover master proposes a library. The proof search attempts to close the affected presentation lines with that library. A failed line can yield a concrete positive-charge wheel. Its configuration incidence gives another covering constraint. The final C replay checks the resulting presentations and configuration sequence independently of this search model. The numerical search covers a finite candidate pool and restricted proof and rule families. It supplies an upper bound on the minimum possible cardinality.

The rule experiments use the original rule vertices and their oriented triangle construction. They derive a proposed local transfer from an axle, add its reflected entry, reprove the affected donor lines and check the recipient degree for newly invalid hubcaps. One such change removed baseline configuration 2411 with no added configurations. This first 2,821-record milestone is preserved in `rulebundles/2411`, including all eight discharging logs and all five reducibility logs.

The published primary bundle passed a second independent invocation of the documented eight-worker replay. All 16 subprocess exits were zero, covering the eight degrees and eight disjoint reducibility shards. [Full replay transcript](final_replay.log) · [Per-process statuses and complete output](best_bundle/logs/)

## Reproducing the selection

The exact selected sequence is listed as one-based record positions in `best_bundle/ids` relative to `fullpool.conf`. Its SHA-256 is `116f9176577e907631e41d49914ab7d22fefb74b09f45801d3418e841d51220e` for the full candidate pool. The independently verified selection and generated presentations are preserved in `fullsearch/`. Replaying the proof needs only the verification commands above.

The final exact HiGHS solve covered 1,971,156 traced states across all eight degrees, giving 341,631 distinct alternative-choice sets. The master protected the original 70-record prefix and used fixed-interior alternatives and the traced root match. After forced choices and redundant rows were removed, 519 constraints on 1,739 columns remained. It reached zero gap at 2,484 records and 91 ring-16 records. The published selection ties that objective and retains four more original records. [Reproduced solver output](cover_replay.log) · [Search driver](final_cover.py)

To rebuild the search utilities for the final exact cover and the finite-model witness tests from their preserved sources, run the following commands in this directory. The exact-cover replay writes its own selection to `cover_replay/`.

```sh
set -eu
sh build.sh
python3 fast_build.py
python3 fast_smoke.py
gcc -O3 -std=gnu89 -w rebranch.c -o rebranch
gcc -O3 -std=gnu89 -w discharge_probe.c -o probe
gcc -O3 -std=gnu89 -w -c match_kernel.c -o match_kernel.o
g++ -O3 -std=c++17 matching.cpp match_kernel.o -o matching
gcc -O3 -std=gnu89 -w -c witness_kernel.c -o witness_kernel.o
g++ -O3 -std=c++17 netpositive.cpp witness_kernel.o -o netpositive
.venv/bin/python final_cover.py fullsearch fullpool.conf cover_replay 2
```

The initial MILP and ring-first models reached exact optima for their respective finite covering constraints. The larger search also used time-limited HiGHS incumbents, fixes suggested by LP relaxations, and cardinality local search seeded by those solutions. Their run logs report solver gaps and failed leaves. These objectives are search diagnostics. A reported certificate count is an upper bound established by the two C verifiers.

| Search input or output | Location |
|---|---|
| Baseline source integrity | [Archive member hashes](sources.sha256) |
| Exact private tail states, 5,213 rows | [Gzipped TSV](tail_axles.tsv.gz) |
| Disk harvesting, D-only streaming and ring 6–16 smoke test | [Harvester](harvest_local.py), [checker driver](fast_driver.c), [test result](fast-smoke.log) |
| Fixed-rule counterexample-guided set cover | [Search log](broader.log), [selected pool](enriched2.conf) |
| Refined-rule construction and repair | [Rule synthesis](newrules.py), [accepted rule stack](combined/11/selection), [refined rules](effective/rules) |
| Refined searches | [MILP log](finalrun.log), [local search](polish.log), [expanded-pool search](fullsearch.log) |
| Ring-first searches | [Original rules](ringstress.log), [refined rules](ringfinal.log) |

## What prevented ring 15

For the original rules and the 19,188-record stress-test pool, the final positive-wheel rows contain 82 pairwise-disjoint sets of exclusively ring-16 choices, including 81 singletons. For the refined rules and 19,662-record pool, there are 75 pairwise-disjoint such sets, including 73 singletons. The ring-first bundles attain these bounds for the corresponding pools and local matching model. Further rule changes or newly discovered configurations can change the incidences. [Original-rule rows](ring_witness_rows.tsv) · [Refined-rule rows](refined_ring_witness_rows.tsv) · [Integer certificate replay](verify_bounds.py)

For the 19,662-record library under the refined rules, 23,895 distinct positive-wheel incidence rows give a lower bound of **2,421** within this local matching model. The integer row weights sum to 2,420,608,825. The largest total weight incident to one candidate is 1,000,002. Therefore any cover of the rows needs at least the ceiling of their ratio. The search reached 2,484, leaving 63 configurations between that result and this model-specific lower bound. Different rules, configurations or embedding models can change the bound. [Integer weights](full_concrete/weights.tsv) · [Incidence matrix](full_concrete/incidence.tsv) · [Completed wheels](complete_wheels.bin)

The following commands regenerate the finite-model matrices with the supplied search executable and check both ring packings and the integer bounds. Every row of each ring packing occurs on a completed wheel with positive charge under the indicated rule file. The limited part of a high-degree peripheral vertex is encoded as the interval from 9 to infinity.

```sh
python3 complete_wheels.py
RULES=baseline/rules ./netpositive stresspool.conf complete_wheels.bin original_concrete.tsv 2822
.venv/bin/python local_bound.py fullpool.conf effective full_concrete complete_wheels.bin
python3 verify_bounds.py
```


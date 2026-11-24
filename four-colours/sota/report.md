# RSST fixed-rule search

**The best complete certificate found has 633 configurations, including 294 D-reducible and 339 requiring a contract.** This equals the RSST cardinality and replaces 45 contract-dependent entries in the count with D-reducible entries. The strict cardinality record remains open. The bundle passed unmodified stock reduction and discharging. Its explicit presentations cover degrees 5 through 11, and it retains the original configurations used in the published high-degree argument. [Full bundle](bundle/) · [Verifier results](verification/bundle/summary.json) · [RSST, §§3–4](https://www.lix.polytechnique.fr/~werner/PI-4C/robertson.pdf)

**The five requested stock discharging runs alone accept 628.** Six changed hubcap instructions in degree 11 allow the fifth deletion after four zero-use entries disappear from the original presentations. A degree-6 positive-charge cartwheel witnesses the need for each of those five originals. The 628 result applies to the degree-7–11 benchmark. [Five-hub bundle](five-hub-628/) · [Verifier results](verification/five-hub-628/summary.json)

| Certificate | Configurations | D | Require C | Degree coverage |
|---|---:|---:|---:|---|
| Original RSST | 633 | 249 | 384 | Published proof |
| Original five presentations, optimized stock subset | 629 | 245 | 384 | 7–11 |
| Six revised degree-11 hubcaps | 628 | 244 | 384 | 7–11 |
| Full search result | 633 | 294 | 339 | Stock runs 5–11, published high-degree lemma retained |

## Exact stock-pool diagnostic

| Hub | Explicit R lines | Calls to Reduce, including H | Axles popped inside Reduce |
|---:|---:|---:|---:|
| 7 | 480 | 40,627 | 49,602 |
| 8 | 387 | 65,371 | 77,304 |
| 9 | 301 | 45,314 | 51,143 |
| 10 | 103 | 10,123 | 10,786 |
| 11 | 27 | 1,264 | 1,312 |
| **Total** | **1,298** | **162,699** | **190,147** |

**162,699** is the corrected call total. Hubcap bounds account for 161,401 calls. A stock upper-degree embedding can require further reductions after lowering a degree. Exactly 255 explicit R lines have no single configuration that proves the entire line on its own. Their successful proofs combine witnesses. [Probe source](discharge_probe.c) · [Stock hub-7 trace](stock/7/events.tsv) · [Recursive single-configuration incidence](stock/7/singleton.tsv)

| Definition of use, across all 633 original entries | 0 uses | 1 use | 2 uses | 3 uses |
|---|---:|---:|---:|---:|
| Explicit R root, stock first match | 370 | 98 | 55 | 45 |
| Explicit R root, all isomorphism-checked upper-degree matches | 366 | 92 | 56 | 48 |
| Explicit R root, configurations independently proving the whole line | 382 | 95 | 53 | 42 |
| Every visited R/H reduction state, stock first match | 4 | 22 | 16 | 16 |
| Every visited R/H reduction state, all checked matches | 4 | 11 | 6 | 10 |

The all-match probe records a one-based pool index and a fixed-degree flag for each accepted embedding. It follows the stock first match for the recursive trace. The companion singleton file independently tries each matching configuration alone through all required degree-lowering children. The wheels file records every degree interval and clockwise triangle. The search fork rejects individual embeddings that fail the stock isomorphism assertion and logs their IDs. Every delivered certificate was replayed through the unmodified verifier. [Instrumented fork](discharge_probe.c) · [Cartwheel dump](stock/7/wheels.tsv)

The stock and stock-plus-33333 root-incidence MILPs both reached **629**, with equal incumbent and lower bound. The stock subset at that value passed all five stock presentations. Appended 33333 had zero upper-degree matches anywhere on the 190,147-state stock trace. The four omissions have one-based positions **8, 12, 19, 21**. The six altered hubcap lines in present11 are **130, 134, 169, 173, 208, 212**. They allow omission of position **14** as well. [629 input and logs](diagnostic629/) · [Revised degree-11 presentation](five-hub-628/present11)

## A certificate of necessity for every original configuration

For each original index the search produced a positive-charge cartwheel matched by that configuration alone from the original 633 plus 33333. There are **628 witnesses of degrees 7–11** and **five witnesses of degree 6**, the latter for exactly the five indices above. Changing a presentation cannot remove the need to cover its positive cartwheels. Thus, within this 634-member pool and the fixed-rule cartwheel argument, the exact minima are **628 for the five hubs** and **633 for all hubs**. This lower bound allows arbitrary rebranching. [633 witnesses](private-witnesses.tsv) · [Independent replay](private-audit.log)

The witness records give degrees, stock charge in tenths and vertex intervals. A non-hub 9+ slot is realized with degree 12. New fan vertices beyond the limited axle can also have degree 12. The tested pattern interiors have maximum degree 11. A separate C++ program constructs the wheel edges, enumerates degree-preserving induced interior injections, enforces well-positioning and checks a common orientation for all finite triangles. This test admits a superset of possible geometric appearances. It found exactly the intended configuration on **every** private witness. The independent test and the stock matcher agreed on all 633 witnesses. The charge replay uses the stock outlet predicates. [Embedding checker](audit_private.cpp) · [Charge and incidence replay](audit_charge.py)

## Degree-five hypothesis

The 512 ordered lists satisfying the stated inequalities form 68 dihedral orbits. The complete table gives the orbit multiplicity, ring, direct extensions, surviving classes, contract endpoints and number of eligible contracts tried. **12 orbits are D, 30 are C, and 26 fail D and every eligible contract through size four.** Counting ordered lists gives 71, 231 and 210 respectively. [All 68 results](h1_results.md)

| Neighbours of the degree-5 hub | Ring | Direct | Survivors | Eligible contracts tested | Result |
|---|---:|---:|---:|---:|---|
| 6,6,6,6,6 | 10 | 530 | 1,220 | 4,109 through first success | Four-edge C |
| 6,6,6,6,7 | 11 | 1,128 | 5,488 | 8,137 | Neither |
| 6,6,6,6,8 | 12 | 2,272 | 18,470 | 9,888 | Neither |
| 6,6,6,6,9 | 13 | 4,612 | 59,452 | 11,901 | Neither |
| 6,6,6,6,10 | 14 | 9,240 | 185,301 | 14,200 | Neither |

The search engine uses 16 OpenMP workers, the stock streaming signed-matching kernel, a sparse triangle mask, the stock triad predicate and stock contract-colouring enumeration. Each worker holds one input configuration and its working arrays. Stock reduce verified all **38 positive H1 representatives within its input degree limit**. Four other positive representatives contain a degree-13 or degree-14 vertex and required the enlarged degree array. The 26 negative results come from exhaustive search, since stock reduce only checks supplied positive certificates. [Engine](fast_reduce.cpp) · [Kernel build](build_reduce.py) · [Stock H1 output](h1_reduce.log)

## Harvest, optimization and rebranching

| Harvest from degree-7–11 traces | Screened | D | Require C | Neither |
|---|---:|---:|---:|---:|
| Triangulated disk interiors | 13,875 | 10,117 | 3,319 | 439 |
| Two triangulated pieces sharing a cut vertex | 4,390 | 2,808 | 1,376 | 206 |
| **Total input records** | **18,265** | **12,925** | **4,695** | **645** |

The disk and cut-vertex searches grow connected interiors from oriented triangles, construct free completions, and apply ring, degree, radius and stock capacity limits. The disk search found 3,120 candidates in traces with multiple original first-witness IDs. Contract search tested sizes one through four, stopping on the first success. Raw positive counts include nonminimal configurations and overlaps with the stock set. Isomorphism deduplication of compatible records, including positive H1 inputs, gave **17,668** configurations in the first combined pool. A further 140 low-degree disk candidates and compatible records from Steinberger's archive brought the final pool to **19,140 distinct shapes**. The complete selected bundle was checked by stock reduce. The entire exploratory pool was screened by the search engine or taken from the source archive. [Disk harvest](harvest.py) · [Cut-vertex harvest](cuts.py) · [Screening results](harvest.tsv) · [Final pool](extended/pool.conf) · [Steinberger's configuration data](https://arxiv.org/src/0905.0043v3/anc/U_2822.conf)

The rebrancher tests stock C degree splits, R reductions, active S symmetries and H hubcaps. It finds pair charge bounds with the stock bound recursion and chooses a minimum-cost double cover by assignment. Additional trials restrict rotations and reflections of existing presentations to a target axle. Positive witnesses reject failed deletions. Completed alternative subtrees remain available as choices in the MILP. The presentation language uses C, H, S and R instructions. L denotes the level. [Rebrancher](rebranch.c) · [Tree restriction](project.c) · [Choice MILP](choice_cover.py)

The final MILP allowed alternative local proofs on **10,295 presentation lines**. Its exact finite-matrix optimum is 633. Among those minimum-cardinality solutions it minimized C entries to 339. The integer objective was 1,000 times cardinality plus the number requiring C. HiGHS returned **633,339** as incumbent and bound; **3,152** source lines selected alternatives. A stock replay independently tested the resulting proof, including the choices of first match and any resulting recursive axles. [Solver summary](final-choice.log) · [Selected bundle](bundle/)

## Fixed-pool lower bounds and Phase 3

The independent checker evaluated all 19,140 patterns on **3,550 positive wheels**, yielding 3,141 distinct incidence rows. Its full row sets agreed with the stock matcher on every wheel. An integer certificate gives these rows total weight **58,625,970,391**. Each configuration covers weight at most **100,000,000**. Consequently at least **587** configurations from this pool are necessary under the fixed rules. This leaves a gap of at most **46** below the verified 633 for this particular pool. Enumerating exchange possibilities on the same rows rules out every replacement of two stock configurations by one new configuration and every replacement of three by two. [Independent incidence](independent/rows.tsv) · [Integer weights](independent/weights.tsv) · [Replay](verify_lower.py) · [Two-for-one enumeration](exchanges.py) · [Three-for-two enumeration](triples.py)

An additional MILP capped cardinality at 632 and minimized the number of added shapes. HiGHS found a minimum of **five additions** on the independently enumerated positive-wheel rows. Thus a globally successful exchange in this pool would have to replace at least six originals. The five-addition incumbent covers the sampled rows. A further degree-9 wheel of charge 1 tenths excludes that incumbent. [Additional witness](finalist-rows/9/axles) [Exchange MILP](exchange_master.py) · [Solver output](independent/master.log)

Changing the rules changes which wheels carry positive charge. Neither the 633 private witnesses nor the 587 bound quantifies the possible saving under different rules. No rule changes were tested.

## Inventory and verifier replay

| Ring | Original D | Original C | Full bundle D | Full bundle C | Five-hub diagnostic total |
|---:|---:|---:|---:|---:|---:|
| 6 | 1 | 0 | 1 | 0 | 1 |
| 7 | 1 | 0 | 1 | 0 | 1 |
| 8 | 4 | 1 | 4 | 1 | 4 |
| 9 | 7 | 1 | 7 | 1 | 7 |
| 10 | 21 | 10 | 21 | 10 | 29 |
| 11 | 44 | 37 | 46 | 36 | 80 |
| 12 | 93 | 82 | 104 | 77 | 175 |
| 13 | 52 | 142 | 69 | 125 | 194 |
| 14 | 26 | 111 | 41 | 89 | 137 |
| **Total** | **249** | **384** | **294** | **339** | **628** |

The 633 full-bundle entries have 633 distinct canonical embedded free completions, allowing cyclic relabelling and reflection. A separate abstract-graph test with the ring distinguished also found zero isomorphic pairs. [Isomorphism audit](abstract-iso.log) Contract sizes 0, 1, 2, 3 and 4 occur 294, 232, 13, 57 and 37 times. The rule file is byte-identical to stock, SHA-256 `4a511a1df9392a7af6253bfcf4dab9bf96ea9a080465abd0b12b57788a6c3dee`. The eight stock configurations explicitly used by the high-degree argument are retained at original indices 1, 3, 6, 9, 24, 26, 139 and 324. Degree 12 was also replayed with the single-edge upper bound five at every spoke. [Full inventory and exit statuses](verification/bundle/summary.json) · [Degree-12 output](verification/degree12/check.log) · [RSST, Lemmas 4.7–4.8](https://www.lix.polytechnique.fr/~werner/PI-4C/robertson.pdf)

From this directory, the following commands rebuild unmodified verifiers, stage each bundle in an isolated working directory, check positive completion messages as well as exit status, and audit its inventory.

```sh
python3 verify.py bundle
python3 verify.py five-hub-628
python3 audit_charge.py
python3 verify_lower.py
```

The stock compiler invocations use `gcc -std=gnu89 -w -O3 ../recon/rsst/reduce.c -o reduce` and `gcc -std=gnu89 -w -O3 ../recon/rsst/discharge.c -o discharge`. The verifier commands in the staged full bundle were `./reduce unavoidable.conf` and `./discharge presentN` for each N from 5 through 11. Every process exited 0. The logs end with these messages.

```text
Reducibility of 633 configurations verified
present5 verified.
present6 verified.
present7 verified.
present8 verified.
present9 verified.
present10 verified.
present11 verified.
```

The five-hub run printed `Reducibility of 628 configurations verified` and `presentN verified.` for N from 7 through 11, all with exit 0. [Full verifier logs](verification/bundle/) · [Five-hub verifier logs](verification/five-hub-628/) · [Verification script](verify.py)


## Rebuild the search tools

Run the following commands from this directory. The MILP commands need NumPy and SciPy. The diagnostic and stock replays use the C compiler and Python standard library.

```sh
python3 probe_build.py
gcc -O3 -std=gnu89 -w discharge_probe.c -o discharge_probe
DUMP=1 python3 scan.py stock-replay ../recon/rsst/unavoidable.conf
python3 cover.py stock-replay ../recon/rsst/unavoidable.conf
python3 build_reduce.py
python3 h1.py
./fast_reduce h1.conf > h1-replay.tsv
python3 branch_build.py
python3 concrete.py build 0
g++ -std=c++20 -O3 audit_private.cpp -o audit_private
python3 audit_charge.py
python3 verify_lower.py
PREFER_D=1 OUT=replayed-choice python3 choice_cover.py extended/stock extended/branch corev
GEOM_ROWS=independent/rows.tsv python3 exchange_master.py
```

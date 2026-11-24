# Phase 4A four-colour certificate

The published certificate has **604 configurations, 284 D-reducible and 320 C-reducible**. This reduces the supplied certificate by 21. The stock reduction checker accepted all 604 configurations and the stock discharging checker accepted each presentation for degrees 5 through 12. All nine runs exited 0. For larger hubs, the degree-12 local proof extends as described below. This meets the target of fewer than 605. The search has not reached the stretch target of fewer than 590. [Certificate](best_bundle/) · [Stock results and hashes](verification/summary.json)

## Changes from the supplied 625

The new bundle removes 38 records and introduces 17 others. The manifest identifies every removed configuration, includes the full text of added records and pinpoints every changed presentation line. The reconstruction script checks the original and output hashes for all ten files. [Exact changes](certificate-edits.json) · [Reconstruction](reproduce.py)

The following table uses the numeric identifiers and interval notation in the rule file. A single digit from 5 through 8 requires that exact degree. In a two-digit guard the first digit sets the lower bound and the second sets the upper bound. A final 9 leaves the upper end open, so `69` accepts every degree at least 6. The table lists each rule with its explicit reflected entry when one is present.

| Entries | Changes |
|---|---|
| 26 | vertex 8 guard removed, vertex 9 guard removed, vertex 12 gains guard `69`, vertex 14 gains guard `69` |
| 29 and 30 | Transfer `7→79` becomes `7→59`, vertex 12 gains guard `69` |
| 31 and 32 | vertex 8 gains guard `69`, vertex 12 changes from `6` to `69` |
| 35 and 36 | Transfer `7→79` becomes `7→69`, vertex 5 changes from `5` to `67` |
| 49 and 50 | vertex 13 changes from `6` to `69` |
| 51 and 52 | vertex 4 changes from `5` to `57`, vertex 8 gains guard `69` |
| 55 and 56 | vertex 14 gains guard `69` |
| 82 and 83 | vertex 8 changes from `5` to `56`, vertex 12 changes from `7` to `69`, vertex 13 changes from `7` to `57` |
| 84 and 85 | Both entries removed |
| 86 and 87 | New transfer `7→7` with guards `2=6`, `3=7`, `4=69`, `5=56`, `6=6`, `9=5`, `14=5`, `15=5`, `16=59` |

- Widening vertex 5 of entry 35 removed `184.1310466` and `184.3686406` together. Widening vertex 13 of entry 49 removed `122.3700802`. [622 replay](verify622/summary.json)
- Reworking degree-7 guards and the degree-8 transfer in entry 82, then repairing the affected presentations, brought the set to 616. [616 replay](verify616/summary.json)
- Replacing the vertex-8 and vertex-9 guards in the self-reflecting entry 26 with lower bounds of 6 at vertices 12 and 14 removed the ring-11 D configuration `123.442817`. [615 replay](verify615/summary.json)
- At 615 the set-cover solver exchanged eight configurations for seven. [614 replay](verify614/summary.json)
- A change to entry 35 shifted its sink threshold to degree 6 and restricted vertex 5 to degrees 6–7. One transfer then removed these six configurations together, `182.1368180`, `142.1324806`, `197.504480`, `3.1369216`, `496.12422`, and `leaf-4412`. [609 replay](verify609/summary.json)
- The six deletions remained valid on the 614-member set-cover result, giving 608. [608 replay](verify608/summary.json)
- Local rebranching removed the ring-12 D configuration `cut8-290`. Later pool exchanges improved the C count. Removing entries 84 and 85 then freed four degree-7 outlets at cardinality 607. [607free replay](verify607free/summary.json)
- One continuation used the spare slots for a new transfer from degree 8 to degrees 6–7. It removed the ring-14 D configuration `leaf-2544` and yielded 606. [606late replay](verify606late/summary.json)
- A different continuation from 607 combined two degree-7 motifs. Entry 55 kept the original bounds when vertex 14 had degree at least 6. When vertex 14 had degree 5, a second 7→7 rule allowed a wider range at vertices 4 and 16. This removed both `186.61866` and `483.3927606`. [605 replay](verify605/summary.json)
- A counterexample-guided exchange replaced two D configurations, `leaf-2327` and `leaf-5010`, with one C configuration, `leaf-484`. Local rebranching closed the affected presentations. [604 replay](verify604/summary.json)

| Count | D | C | Checkpoint |
|---:|---:|---:|---|
| 622 | 291 | 331 | [First combined rule pair](verify622/summary.json) |
| 620 | 290 | 330 | [Joint guard tightening and widening](verify620/summary.json) |
| 619 | 289 | 330 | [Combined discharging edits](verify619/summary.json) |
| 617 | 288 | 329 | [Repaired presentations](verify617/summary.json) |
| 616 | 287 | 329 | [Further degree-8 relief](verify616/summary.json) |
| 616 | 289 | 327 | [Expanded-pool exchange](verify616milp/summary.json) |
| 615 | 288 | 327 | [Self-reflecting degree-7 transfer](verify615/summary.json) |
| 614 | 287 | 327 | [Set-cover exchange](verify614/summary.json) |
| 609 | 285 | 324 | [Six configurations removed by one transfer edit](verify609/summary.json) |
| 608 | 284 | 324 | [Combined with the set-cover exchange](verify608/summary.json) |
| 607 | 283 | 324 | [Deletion by local rebranching](verify607/summary.json) |
| 607 | 285 | 322 | [C-reducibility tie-break improvement](verify607milp/summary.json) |
| 607 | 286 | 321 | [One newly harvested D configuration](verify607late/summary.json) |
| 607 | 286 | 321 | [Same configurations with four fewer degree-7 outlets](verify607free/summary.json) |
| 606 | 284 | 322 | [Relief from degree 8 to degrees 6–7](verify606/summary.json) |
| 606 | 285 | 321 | [Relief transfer with the harvested configuration](verify606late/summary.json) |
| 605 | 285 | 320 | [Combined degree-7 motifs](verify605/summary.json) |
| 604 | 283 | 321 | [Two-for-one exchange with local rebranching](verify604/summary.json) |
| 604 | 284 | 320 | [Expanded-pool C-count tie-break](verify604milp/summary.json) |

## Verification

| Hub degree | Stock outlets | Presentation instructions | Maximum level | Stock exit |
|---:|---:|---:|---:|---:|
| 5 | 10 | 353 | 5 | 0 |
| 6 | 28 | 65,757 | 10 | 0 |
| 7 | 107 | 6,285 | 11 | 0 |
| 8 | 72 | 5,901 | 10 | 0 |
| 9 | 57 | 3,293 | 10 | 0 |
| 10 | 57 | 1,017 | 8 | 0 |
| 11 | 57 | 363 | 11 | 0 |
| 12 | 57 | 1 | 0 | 0 |

The stock reduction log ends with `Reducibility of 604 configurations verified`. Embedded canonicalization produced 604 distinct forms. Ring-preserving graph invariants separated all but 1 candidate pair. Exact graph isomorphism distinguished the remaining pair. All 604 ring-distinguished abstract graphs are distinct. [Reduction log](verification/unavoidable.conf.log) · [Verification code](audit.py)

| Ring | D | C | Total |
|---:|---:|---:|---:|
| 6 | 1 | 0 | 1 |
| 7 | 1 | 0 | 1 |
| 8 | 4 | 1 | 5 |
| 9 | 7 | 1 | 8 |
| 10 | 20 | 10 | 30 |
| 11 | 46 | 36 | 82 |
| 12 | 100 | 73 | 173 |
| 13 | 63 | 121 | 184 |
| 14 | 42 | 78 | 120 |

The rule audit checks source upper degree, degree intervals, template predecessors, distinct template positions, and both source and sink orientations. It found 35 explicit mirror pairs and the three unpaired entries 21, 26 and 63. For each unpaired entry the audit explicitly reflected all template positions and proved that its guards are invariant. The maximum source upper bound is 8. The highest outlet count is 107, below the stock cap of 108. [Rule audit](rulespec.py) · [Machine-readable results](verification/summary.json)

### Degrees above 12

The degree-12 presentation proves twelve identical single-edge inequalities, each bounding incoming charge by five tenths. The 57 degree-12 outlets are all incoming and refer only to spoke offsets −2 through +2 from the distinguished edge. At larger hub degrees the same degree intervals select the same incoming patterns. The source upper bound excludes outgoing patterns at these hubs. [Degree-12 presentation](best_bundle/present12) · [Stock log](verification/present12.log)

In the single-edge proof, forcing an outlet can give finite upper bounds only in those five columns. Every selected configuration has maximum interior degree at most 11. Hence its interior image avoids the hub and vertices with unconstrained upper degree. A recursive reduction lowers upper bounds only at interior images. Inserting spokes on the opposite side preserves the local adjacencies, fan triangles and well-positioning checks throughout this proof. The stock checker’s verbose replay independently exposes 60 configuration images across the twelve edges. The nonhub image positions, including any auxiliary ring vertices printed by the checker, use only offsets `-2, -1, 0, 1`. No configuration interior contains the hub. The trace records 0 recursive upper-bound decreases. [Stock trace audit](verification/summary.json)

Each edge therefore retains its five-tenths bound. For degree `d ≥ 12` the total charge in tenths is at most `10(6 − d) + 5d = 60 − 5d ≤ 0`.

## Search and bounds

The search ranked configurations by their presentation leaves, generated relief motifs from failing axles and screened candidates on concrete wheels. It tested new degree-8 transfer pairs, degree-7 sink redirections, removal of existing transfers, simultaneous tightenings, and rules shared across multiple candidate deletions. Pair-bound optimization and balanced local rebranching repaired affected presentations. Repeating the search after successful batches accounted for the sequence of verified checkpoints above. [Transfer search](search8.log) · [Joint edits](partition.log) · [Degree-7 redirections](redirects.log) · [Later candidate search](round7.log) · [Multi-rule synthesis](model607.log) · [Batched degree-8 tests](batch607.log)


A separate run tested 5,941 symmetric transfer candidates, including changes to the three inherently symmetric stock rules and additions that fit in the last degree-7 slot. Counterexample-guided screening reused 370 newly found wheels. On 328 of these wheels the matcher found no member of the incumbent. [Symmetric transfer synthesis](symmetric.log) · [Symmetric rule edits](symmetric-edits.log) · [Replay search](symmetric-final.log)

Among 10,132 sampled degree-8 wheels, the matcher found **168 distinct final configurations** with a positive wheel on which it was the sole matched bundle member and all eight spokes had degree at most 7. An added 8→8+ or 8→9+ transfer can neither send nor receive charge at the hub on those wheels. Outlet headroom alone therefore cannot remove those configurations using the specified additions on the same bundle. [Witnesses](verification/degree8-private.tsv) · [Recheck](obstruction_audit.py)

At 604, a further sweep screened 85,087 rule variants. Subsequent searches tried combining two degree-8 transfers and looked for 603-member exchanges in the expanded pool, allowing up to six additions per exchange. The final searches produced no smaller verified certificate. [Rule sweep](round12.log) · [Combined transfers](multi8.log) · [First exchange search](exchange604.log) · [Final exchange search](exchange604milp.log)

On 119 counterexample wheels, disk extraction produced 806 candidates. The fast reducer accepted 742. Embedded canonicalization identified 544 additions to the existing pool, giving 19,689 candidates. Separately, enumeration inside the 616-member pre-exchange bundle yielded 651 eligible disk shapes, including 108 absent from the pool. None of those 108 passed the fast reduction screen. A second extraction targeted 279 positive private wheels. Of 2,645 compatible disks, 2,530 passed the fast screen and 1,648 were new, taking the search pool to 21,337. [Second harvest](lateharvest.log) [Counterexample harvest](harvest.log) · [Subdisk enumeration](subdisks.log)

The joint MILP minimizes `1000 × cardinality + C count`. At cardinality 607, a diversity search exchanged 81 records relative to the 322-C solution and supplied another starting point for rule edits. [Diversity model](diverse607.log) · [Diverse-seed search](round10.log)

The compact models include additional proofs found by rebranching with other pool configurations. Before solving, the program discards equivalent proof choices and rows already covered by mandatory singleton configurations. On the 604-member seed it generated 12,627 proof choices in 13,411 attempts. The compact model and the full-row model both attained 604,320. This proves optimality for their respective rule sets, presentations, pools and enumerated proofs. The minimum over all possible certificates remains open. [Final alternative proofs](alt-pool604.log) · [Compact solve](compact604.log)

| Model | Pool | Mandatory rows | Alternative proofs | Chosen | Objective | Solver bound |
|---|---:|---:|---:|---:|---:|---:|
| [milp622.log](milp622.log) | 19,145 | 59,299 | 1,501 | 622 | 622,331 | 622,331 |
| [milp-harvest.log](milp-harvest.log) | 19,689 | 59,397 | 1,501 | 622 | 622,331 | 622,331 |
| [milp619.log](milp619.log) | 19,689 | 56,157 | 1,703 | 619 | 619,329 | 619,329 |
| [milp617.log](milp617.log) | 19,689 | 53,170 | 1,734 | 617 | 617,327 | 617,327 |
| [milp616.log](milp616.log) | 19,689 | 49,578 | 2,048 | 616 | 616,327 | 616,327 |
| [compact616.log](compact616.log) | 19,689 | 5,549 | 2,720 | 616 | 616,327 | 616,327 |
| [milp615.log](milp615.log) | 19,689 | 50,171 | 1,984 | 614 | 614,327 | 614,327 |
| [compact615.log](compact615.log) | 19,689 | 6,789 | 3,081 | 614 | 614,327 | 614,327 |
| [milp614.log](milp614.log) | 19,689 | 47,386 | 2,302 | 614 | 614,327 | 614,327 |
| [milp615b.log](milp615b.log) | 19,689 | 48,294 | 2,110 | 614 | 614,327 | 614,327 |
| [milp608.log](milp608.log) | 19,689 | 50,211 | 1,900 | 608 | 608,322 | 608,322 |
| [milp607.log](milp607.log) | 19,689 | 47,688 | 2,123 | 607 | 607,322 | 607,322 |
| [milp-late.log](milp-late.log) | 21,337 | 47,148 | 2,297 | 607 | 607,321 | 607,321 |
| [milp-late-pool.log](milp-late-pool.log) | 21,337 | 8,371 | 3,954 | 607 | 607,321 | 607,321 |
| [milp-release.log](milp-release.log) | 21,337 | 47,235 | 2,294 | 607 | 607,321 | 607,321 |
| [milp606.log](milp606.log) | 21,337 | 47,590 | 2,284 | 606 | 606,321 | 606,321 |
| [milp605.log](milp605.log) | 21,337 | 47,637 | 2,283 | 605 | 605,320 | 605,320 |
| [milp604.log](milp604.log) | 21,337 | 50,360 | 1,992 | 604 | 604,320 | 604,320 |
| [compact604.log](compact604.log) | 21,337 | 9,855 | 4,001 | 604 | 604,320 | 604,320 |

## Reproduction

Run from `four-colours/sota_rules_v2`. Stock replay requires GCC, Python 3 and NetworkX. The scripts keep generated outlet files and binaries outside the certificate. This host provides the Python dependencies at the path used below.

```sh
export PYTHON=/tmp/recon-fc/venv/bin/python
. ./dependencies.sh
./verify.sh best_bundle
"$PYTHON" -B reproduce.py reproduced
diff -qr best_bundle reproduced
"$PYTHON" -B obstruction_audit.py best_bundle
```

To run the stock programs directly in a local temporary directory, use the following commands.

```sh
set -eu
work=$(mktemp -d "$PWD/stock-replay.XXXXXX")
gcc -std=gnu89 -O3 -w ../recon/rsst/reduce.c -o "$work/reduce"
gcc -std=gnu89 -O3 -w ../recon/rsst/discharge.c -o "$work/discharge"
cp best_bundle/* "$work/"
(
    cd "$work"
    ./reduce unavoidable.conf > reduce.log
    tail -n 1 reduce.log | grep -Fx 'Reducibility of 604 configurations verified'
    for d in 5 6 7 8 9 10 11 12
    do
        ./discharge "present$d" > "present$d.log"
        tail -n 1 "present$d.log" | grep -Fx "present$d verified."
    done
)
```

To reproduce the expanded 616-stage model, use the following commands. The `bin/select` and `bin/hard` search executables are used only to propose proof choices. The independent stock verifier compiles both checkers directly from their upstream C sources.

```sh
export PYTHON=/tmp/recon-fc/venv/bin/python
. ./dependencies.sh
export WORKERS=4 COVER_DIR=recheck-cover COVER_RESULT=recheck-result
export ALT_SRC=unions/dd7a4fa4be8f HARVEST_FILE=harvest/combined.conf
"$PYTHON" -B cover.py gather "$ALT_SRC"
"$PYTHON" -B alternatives.py 8500
"$PYTHON" -B cover.py solve "$ALT_SRC"
"$PYTHON" -B pool_alternatives.py 7000
COMPACT=1 "$PYTHON" -B cover.py solve "$ALT_SRC"
```

The next model starts from the stock-verified 615-member bundle with the changed rule 26. This is the solve that first selected 614 configurations.

```sh
export ALT_SRC=symwins/b21de4199625-109 COVER_DIR=recheck-615 COVER_RESULT=result-615
"$PYTHON" -B cover.py gather "$ALT_SRC"
"$PYTHON" -B alternatives.py 8500
"$PYTHON" -B cover.py solve "$ALT_SRC"
PYTHON="$PYTHON" AUDIT_DIR=verify-recheck-615 ./verify.sh "$COVER_RESULT"
```

The 607-member replay with the C-count tie-break can be reproduced from the rebranched bundle as follows.

```sh
export ALT_SRC=bare608/570 COVER_DIR=recheck-607 COVER_RESULT=result-607
export HARVEST_FILE=harvest/combined.conf
"$PYTHON" -B cover.py gather "$ALT_SRC"
"$PYTHON" -B alternatives.py 9000
"$PYTHON" -B cover.py solve "$ALT_SRC"
PYTHON="$PYTHON" AUDIT_DIR=verify-recheck-607 ./verify.sh "$COVER_RESULT"
```

To repeat the search that found the two-for-one exchange, use the 605-member seed, its leaf ranking and the expanded wheel incidence file. The search verifies candidate presentations with the repair engine. Run the stock verifier on any selected output. The search reuses observed wheels from `exchange605-wheels.jsonl`. A later run can encounter them in a different order. The manifest reconstruction above reproduces the published files byte for byte regardless of solver tie choices.

```sh
export SRC=fusionwins/f7c70ebf0957 COVER_DIR=rank605
export WHEEL_POOL=poolscan21/combined.conf EXCHANGE_WINS=recheck-exchanges
"$PYTHON" -B exchange605.py
```

To repeat the 604-member tie-break with the final harvested pool, use the verified two-for-one exchange as the model input. The first solve selected the published 284-D, 320-C bundle. The compact solve repeats the objective check with additional leaf proofs.

```sh
export WORKERS=4 HARVEST_FILE=lateharvest/combined.conf
export ALT_SRC=ex605wins/39f6590595fb COVER_DIR=recheck-604 COVER_RESULT=result-604
"$PYTHON" -B cover.py gather "$ALT_SRC"
"$PYTHON" -B alternatives.py 8500
"$PYTHON" -B cover.py solve "$ALT_SRC"
AUDIT_DIR=verify-recheck-604 ./verify.sh "$COVER_RESULT"
"$PYTHON" -B pool_alternatives.py 13411
COMPACT=1 COVER_RESULT=result-604-compact "$PYTHON" -B cover.py solve "$ALT_SRC"
```

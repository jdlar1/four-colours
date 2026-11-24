# Public four-colour proof files

All four requested RSST files returned HTTP 200 on 2026-11-23. The directory URL ending in `/FC/` returned an empty index. Thomas's proof guide links to the files under `/OLDFTP/four/`. The four downloads below are preserved byte-for-byte in `rsst/`. [Thomas's file and format guide](https://thomas.math.gatech.edu/FC/ftpinfo.html)

| Download | Bytes | SHA-256 |
|---|---:|---|
| [unavoidable.conf](https://thomas.math.gatech.edu/OLDFTP/four/unavoidable.conf) | 407,769 | `1c92fc280a9b384f736b94077fc59aac75e3d830d441ffd2d18683ee4b524e84` |
| [rules](https://thomas.math.gatech.edu/OLDFTP/four/rules) | 2,625 | `4a511a1df9392a7af6253bfcf4dab9bf96ea9a080465abd0b12b57788a6c3dee` |
| [reduce.c](https://thomas.math.gatech.edu/OLDFTP/four/reduce.c) | 30,185 | `f49caf1bffe3721f2c45c9fadcf13f45f058a4c744d858ed35d6c2bf6872ec77` |
| [discharge.c](https://thomas.math.gatech.edu/OLDFTP/four/discharge.c) | 55,569 | `b2e16d710b66b54ef193615f3901636c8361a820b01e2ef7e37d4331318aba19` |

Each blank-line-delimited configuration has an identifier, four header integers, a contract, one cyclic neighbour list per vertex, and packed coordinates. The header gives total vertices, ring size, directly extending classes and remaining consistent classes. The first ring-size vertices form the boundary in order. A positive remaining count identifies a configuration that needs a contract. The contract row starts with its edge count and gives endpoint pairs. The `rules` file has 32 named rules with 67 numbered entries, including 32 inversions.

## Counts from the configuration records

| Ring | RSST D | RSST requiring C | RSST total | Steinberger D |
|---:|---:|---:|---:|---:|
| 6 | 1 | 0 | 1 | 1 |
| 7 | 1 | 0 | 1 | 1 |
| 8 | 4 | 1 | 5 | 5 |
| 9 | 7 | 1 | 8 | 15 |
| 10 | 21 | 10 | 31 | 58 |
| 11 | 44 | 37 | 81 | 184 |
| 12 | 93 | 82 | 175 | 473 |
| 13 | 52 | 142 | 194 | 740 |
| 14 | 26 | 111 | 137 | 745 |
| 15 | 0 | 0 | 0 | 439 |
| 16 | 0 | 0 | 0 | 161 |
| **Total** | **249** | **384** | **633** | **2,822** |

The RSST contract sizes 0, 1, 2, 3 and 4 occur 249, 264, 15, 61 and 44 times, respectively. The stock C verifier confirmed all 633. The stock discharging verifier accepted each of the five presentations for hub degrees 7 through 11. The corresponding numbers of outlets were 103, 64, 53, 53 and 53.

| Vertex count | RSST free completions | Steinberger free completions | RSST interiors | Steinberger interiors |
|---:|---:|---:|---:|---:|
| 4 | 0 | 0 | 3 | 2 |
| 5 | 0 | 0 | 4 | 4 |
| 6 | 0 | 0 | 19 | 15 |
| 7 | 0 | 0 | 82 | 63 |
| 8 | 0 | 0 | 219 | 252 |
| 9 | 0 | 0 | 221 | 635 |
| 10 | 1 | 1 | 65 | 877 |
| 11 | 1 | 1 | 18 | 683 |
| 12 | 1 | 0 | 2 | 256 |
| 13 | 2 | 3 | 0 | 34 |
| 14 | 3 | 2 | 0 | 1 |
| 15 | 4 | 10 | 0 | 0 |
| 16 | 15 | 10 | 0 | 0 |
| 17 | 15 | 34 | 0 | 0 |
| 18 | 49 | 39 | 0 | 0 |
| 19 | 45 | 115 | 0 | 0 |
| 20 | 106 | 164 | 0 | 0 |
| 21 | 133 | 246 | 0 | 0 |
| 22 | 106 | 429 | 0 | 0 |
| 23 | 102 | 323 | 0 | 0 |
| 24 | 36 | 530 | 0 | 0 |
| 25 | 13 | 319 | 0 | 0 |
| 26 | 1 | 321 | 0 | 0 |
| 27 | 0 | 160 | 0 | 0 |
| 28 | 0 | 92 | 0 | 0 |
| 29 | 0 | 23 | 0 | 0 |

## Steinberger's archive

The direct text download returned HTTP 200 and 1,831,459 bytes. Its SHA-256 is `61768599e85a45ff9bc884de06918d99c2c08cf68a6ad1048edd5d5f6f83c74d`. All 2,822 records have an empty contract and zero remaining consistent classes. The arXiv source archive contains the same data, a graphical catalogue, the rule set `L_42`, seven discharging scripts, and the author's C verifiers. [Configuration data](https://arxiv.org/src/0905.0043v3/anc/U_2822.conf) · [Author's README](https://arxiv.org/src/0905.0043v3/anc/README) · [Source archive](https://arxiv.org/src/0905.0043v3) · [Paper](https://arxiv.org/abs/0905.0043)

The archived verifier raises the maximum ring size to 16. Its depth-indexed `weight` and `choice` arrays still have eight slots for one-based indexing. Its diagnostic print table ends at ring 14. For a full replay I enlarged the temporary arrays and completed the diagnostic table in a build copy. All 2,822 records passed in eight disjoint batches. The downloaded configuration files were the inputs throughout. [Archived verifier source](https://arxiv.org/src/0905.0043v3/anc/reduce.c)

Run these commands from this directory to regenerate the tables and both reducibility checks.

```sh
curl -fsSL https://arxiv.org/src/0905.0043v3/anc/U_2822.conf -o /tmp/U_2822.conf
python3 asset_counts.py rsst/unavoidable.conf /tmp/U_2822.conf
gcc -O2 -std=gnu89 -w rsst/reduce.c -o /tmp/rsst-reduce
/tmp/rsst-reduce rsst/unavoidable.conf
curl -fsSL https://arxiv.org/src/0905.0043v3/anc/reduce.c -o /tmp/steinberger.c
sed -e 's/weight\[8\]/weight[9]/g' -e 's/choice\[8\]/choice[9]/g' \
    -e 's/interval\[10\]/interval[18]/g' \
    -e 's/428506L, 1485003L};/428506L, 1485003L, 5178161L, 18155816L};/' \
    /tmp/steinberger.c > /tmp/steinberger16.c
gcc -O3 -march=native -std=gnu89 -w /tmp/steinberger16.c -o /tmp/steinberger16
/tmp/steinberger16 /tmp/U_2822.conf
```

# Phase 2, Thrust 2 memo: wheel reducers, discharging pockets, and the convex-cone barrier

Prepared for `gpt-6.2-astra` (Phase 3) on 2026-11-23. Each claim carries a status tag:

- **[PROVED]** has a complete argument here.
- **[VERIFIED]** was established by exact or numerical computation over the stated range.
- **[HEURISTIC]** is supported by an argument, not a proof.
- **[PROPOSAL]** is work for Phase 3.

No repository files were changed. Scripts and logs are in the scratchpad (§10).

## 0. Headlines

1. **[PROVED] Cycle-reducer criterion.** A k-cycle reducer (dual: the wheel W_k) accepts a boundary word exactly when the induced ring vertex colouring uses at most three colours. At k = 10 it accepts 1,023 labelled words (2^k − 1) in 171 classes.
2. **[VERIFIED] Why the wheel reduces 33333.** No D-survivor of 33333 misses a colour on the ring. The fact is real but not local:
   - Kempe moves within the wheel words certify only 50 of the 171 wheel classes, including the 25 direct ones.
   - The full certificate passes through 655 non-wheel classes and needs up to 13 rounds.
   - Under a null model the coincidence would have probability about 2^−146.
3. **[VERIFIED] The wheel fails on the neighbouring cases.** It fails on 43333 = 5[7,6⁴], on both embeddings of 5[5,6,6,6,7], and on 6[6⁶]. On 43333, 43332 and 43323 it still fails under the stronger block-count LP: 220, 76 and 72 wheel classes survive.
   - Among the 26 radius-1 hubs of ring ≤ 10 that are not D-reducible, it passes 10: 33333 and nine hubs that contain an 8-neighbour and at least two 5-neighbours.
   - Among the 20,878 disks of ring 10 with at most one interior vertex, the wheel is the only one that reduces 33333.
   - Of the 26 hubs, 12 have no passing disk with at most one interior vertex, including both embeddings of 5[5,6,6,6,7] and 44322 = 5[7,7,6,5,5].
4. **[PROVED] Cone collapse.** In any convex model of exteriors, several reducers prove no more than the best single reducer. Reducibility reduces to one max-support LP plus a disjointness test.
5. **[VERIFIED for k = 4..9] Kempe relations equal Birkhoff–Lewis.** The intersection over palettes of the signed-matching block spans equals the BL span, with dimension the Riordan number R_k.
   - Consequence: adding BL to the block-count LP never changes it.
   - Confirmed on all 73 hubs tested, rings 5–10: the BL and B supports were identical labelled sets. The same holds at ring 11 on 43333: 5,334 classes in both, and rank(BL) = 1,585 = R₁₁.
6. **[VERIFIED] The full block-count LP adds little beyond D.**
   - It removes between 0% and 18.9% of D-survivors on the 26 ring 8–10 hubs, and 17 of them gain nothing. On 43333 (ring 11) it removes 2.8%.
   - No disk with at most one interior vertex passed under B that failed under D.
   - L alone (BL relations only) allows more classes than D in 22 hubs and the same number in 3. It allows fewer only for 43323 (1,385 classes against 1,408).
7. **[PROVED] Facts about RSST discharging.**
   - An RSST degree-5 vertex can end with positive charge only if it has a degree-5 neighbour. So 33333 and 43333 never arise as positive hubs, and adding 33333 to RSST saves nothing.
   - The six-relay rules 2–7 (14 of 67 entries) are the price of 5s with at most one neighbour of degree ≥ 7: the m = 0 pockets, now reducible, and the "lonely" m = 1 pockets.
   - The lonely-5 family 5[d,6⁴] has ring d + 4, so it is infinite. A finite list of fixed configurations cannot exclude it.
8. **[VERIFIED + HEURISTIC] The obstruction to a short proof.**
   - With the interior fixed, the direct fraction decays by about 0.69 per ring vertex. The survivor fraction rises from 49.6% at ring 10 to 94.0% at ring 14.
   - For convex and linear methods, per-configuration power is capped near D by items 4–6.
   - Lonely 5s force charge to travel distance 2. That pushes configurations to rings 12–14, where RSST has 506 of its 633.

## 1. Conventions

- **Tait colours.** Tait colours {0,1,2} are identified with F₂² \ {0} = {1,2,3}. A labelled boundary word is t ∈ {1,2,3}^k with Σ tᵢ = 0. There are W_k = (3^k + 3(−1)^k)/4 of them: 1,641, 4,920, 14,763 and 44,286 for k = 8..11.
- **Ring vertex colours.** In the dual triangulation the ring vertices get c₀ = 0 and c_j = t₁ + … + t_j. Consecutive values differ by a nonzero t, so the colouring is proper.
- **Classes.** Classes are taken modulo GL₂(F₂) ≅ S₃.
- **Gap notation.** A hub of degree d with gaps g₁…g_d has neighbours of degree gᵢ + 3 and ring k = Σgᵢ − d. So 33333 = 5[6⁵], 43333 = 5[7,6⁴], 43332 = 5[7,6,6,6,5], 43323 = 5[7,6,6,5,6] and 333333 = 6[6⁶].
- **Notation.** For a disk or configuration X:
  - c_X(t) is the number of Tait colourings of X extending t.
  - Dir(X) = supp c_X.
  - S_D(X) is the set of survivors of the signed-matching closure (the standard D-process).
- **Count vectors.** For a planar exterior G, N_G(t) is the number of its colourings inducing t.

## 2. Cycle and wheel reducers

**Lemma 2.1 [PROVED] (k-cycle criterion).** Let R be a cubic k-cycle with one terminal edge at each vertex; dually this is the wheel W_k. A word t ∈ {1,2,3}^k extends across R if and only if Σt = 0 and the prefix set P(t) = {0, s₁, …, s_{k−1}} misses an element of F₂². The number of extensions is c_R(t) = 4 − |P(t)|.

*Proof.* Tait colourings of a cubic plane graph correspond to proper 4-face-colourings modulo translation by F₂². The edge colour is the sum of the colours of its two faces. Fix the outer ring face colours as the prefix sums c_j = s_j; the closing condition is Σt = 0. The only other face is the inner k-face, which touches every ring face. Its colour must avoid P(t), so it has exactly 4 − |P(t)| choices. ∎

**Corollary 2.2 [PROVED].** The labelled count is |B(C_k)| = 2^k − 1 for even k and 2^k − 2 for odd k. The class counts are 85, 171, 341 and 683 for k = 9..12.

*Proof.* Fix c₀ = 0. Proper colourings of C_k inside a fixed 3-set containing 0 number (2^k + 2(−1)^k)/3, and there are three such 3-sets. Each 2-set containing 0 lies in two of the 3-sets and contributes [k even] colourings. Inclusion–exclusion gives 2^k + 2(−1)^k − 3[k even]. ∎

Adding back the 2-coloured words with their two hub colours gives 1,026 at k = 10. This matches report.md's "1,026 rim assignments".

**Lemma 2.3 [PROVED] (disk replacement is always safe).** Let G be a counterexample with the fewest vertices. Let C be a configuration with ring cycle R and interior I, where |I| ≥ 2. Let D be any near-triangulation of a k-gon with fewer than |I| interior vertices. Glue D into R in place of I, keeping the ring order, to get G′. Then G′ is planar, has no loops and has fewer vertices. So G′ is 4-colourable, and its restriction to the exterior gives a word in supp N_G ∩ supp c_D.

*Proof.* The embedding is the disk embedding. A chord of D may duplicate an exterior chord, but parallel edges do not affect colourability. D identifies no ring vertices, so no loops arise. ∎

No connectivity hypothesis is needed. RSST's contract conditions (sparse, |X| ≤ 4, a triad when |X| = 4) are there to control G/X when contraction can identify ring vertices. Wholesale replacement never does that.

**Remark 2.4 (the wheel is outside RSST's search space).** For the cap, the wheel equals contracting the interior to one vertex. This is a 5-edge contract (the hub spokes). Each interior triangle hub–uᵢ–u_{i+1} contains two contract edges. So the contract breaks both sparsity and |X| ≤ 4. RSST-style search on 33333 does succeed, but with a different certificate: five 4-edge contracts (report.md).

### 2.5 When do wheels win? [VERIFIED]

The test is: the wheel passes C exactly when every survivor in S_D(C) uses all four colours on the ring. Equivalently, every ring colouring with a missing colour is certified.

Below, "overlap" is |wheel ∩ S_D| over |wheel classes|. Every hub not shown has zero D-survivors.

| Hub (gaps) | Dual | Ring | Survivors | Overlap | Wheel passes? |
|---|---|---:|---:|---:|---|
| 33333 | 5[6⁵] | 10 | 1,220 | 0/171 | yes |
| 52222 | 5[8,5⁴] | 8 | 100 | 0/43 | yes |
| 53222, 52322 | 5[8,6,5³], 5[8,5,6,5,5] | 9 | 305 each | 0/85 | yes |
| 522222 | 6[8,5⁵] | 9 | 305 | 0/85 | yes |
| 53232, 52332 | 5[8,…] | 10 | 910 each | 0/171 | yes |
| 532222, 523222, 522322 | 6[8,…] | 10 | 910 each | 0/171 | yes |
| 42422 | 5[7,5,7,5,5] | 9 | 376 | 24/85 | no |
| 43223 | 5[7,6,5,5,6] | 9 | 352 | 30/85 | no |
| 43322 | 5[7,6,6,5,5] | 9 | 356 | 32/85 | no |
| 44222 | 5[7,7,5,5,5] | 9 | 320 | 48/85 | no |
| 43332 | 5[7,6,6,6,5] | 10 | 1,320 | 78/171 | no |
| 43323 | 5[7,6,6,5,6] | 10 | 1,408 | 92/171 | no |
| 43242, 43422, 44322, 44232 | | 10 | 1,312, 1,698, 1,664, 976 | 56, 100, 122, 96 | no |
| 442222, 422422 | 6[7,7,5⁴], 6[7,5,5,7,5,5] | 10 | 976, 1,182 | 96, 88 | no |
| 52422, 53223, 53322, 54222 | 5[8,…] | 10 | 1,660, 1,588, 1,605, 1,538 | 56, 70, 75, 112 | no |
| 43333 | 5[7,6⁴] | 11 | 5,488 | 272/341 | no |
| 333333 | 6[6⁶] | 12 | 14,061 | 327/683 | no |

**Disk census, at most one interior vertex.**
- The census covers 0 interior vertices (all chord triangulations) and 1 interior vertex (a hub joined to a ring subset S with |S| ≥ 3, pockets triangulated). There are 1,419, 5,434 and 20,878 such disks at k = 8, 9, 10.
- Passing disks, identical under D and under B (§6.4):
  - 33333 has exactly one passing disk, the wheel. report.md's plantri census agrees: 1 disk with one interior vertex, 237 with at most five.
  - Other hubs: 52222 has 51; 44222 has 86; 52322, 53222 and 522222 have 168 each; 54222 has 57; 442222 and 44232 have 259 each; and the five 910-survivor hubs have 582 each.
  - The remaining 12 hubs have none. They include both embeddings of 5[5,6,6,6,7] and 44322 = 5[7,7,6,5,5]. For comparison, RSST #117 has 17 vertices and ring 10 (7 interior vertices, against the closed hub's 6). It contains the 5[7,7,6,5,5] pattern, has 284 remaining classes against the closed hub's 1,664 survivors, and reduces with a 1-edge contract.

**Wheels versus contracts [PROVED dictionary, HEURISTIC rule].**
- A j-edge contract on a configuration with n interior vertices yields a disk with n − j interior vertices. RSST allows j ≤ 4 with sparsity, so for a 5-cap (n = 6) its contracts leave 2 to 5 interior vertices. The wheel is the extreme j = n − 1.
- For 33333 the passing disk with 1 interior vertex is unique (the wheel), and so is the one with 2 (report.md's census). If RSST's 4-edge contract (five solutions, all rotations) yields a simple disk, that disk must be this unique 2-vertex one. I did not check the contraction directly.
- A contract keeps most of the interior, so its accepted words resemble Dir(C). It wins when the survivors are close to Dir(C) in Kempe distance.
- The wheel discards the interior, so it wins only when all survivors share one global property: every ring colour is present.
- That happened for 33333 and for nine hubs with an 8-neighbour and at least two 5-neighbours. Within a gap family it did not survive a ring increase: 33333 passes, while 43333 (ring 11) and 333333 (ring 12) fail.

## 3. Question (a): why does the wheel avoid the 1,220 survivors? [VERIFIED]

| Smallest ring colour multiplicity m | Certified (incl. direct) | Survivors |
|---:|---:|---:|
| 0 (wheel words) | 171 | 0 |
| 1 | 660 | 530 |
| 2 | 410 | 690 |

At ring 10 with four colours, m ≤ 2. The totals check: 1,241 certified and 1,220 survivors make 2,461.

**The disjointness is not visible inside the wheel class.**

- **Restricted closure.** Run the D-process allowing only wheel classes to be certified. It certifies 25 more classes in round 1 and then stalls at 50 of 171 (25 direct plus 25).
- **Ancestral certificate.** A greedy backward certificate for all 171 wheel classes uses 826 classes: 453 direct and 655 non-wheel. Its depth is 13, the full depth of the D-process.
- **Topology.** View a ring colouring as a closed walk on the tetrahedron K₄ and record its winding vector. Winding does not separate survivors from certified classes:
  - Wheel words have winding (0,0,0,0) or (0,0,0,2), and both values contain survivors from other words: 190 and 95 of them.
  - The 30 classes with winding (0,0,1,3) or (0,1,2,3) all survive.
  - Every other winding value is mixed.
- **Not accidental.** The survivor rate is 49.6%. If survivors were independent of wheel membership, missing all 146 non-direct wheel classes would have probability about 2^−146. For contrast, in 43333 the rate among non-direct wheel classes is 272/299 = 91%, against 74% overall. In 43332 it is 78/137 = 57%, against 54%.

**Conclusion.** The wheel property of 33333 is a global property of the Kempe closure; I found no structural shortcut. Any human proof must show directly that ring colourings with a missing colour are certified, with the D₅ symmetry as the only obvious compression. The task is posed in §9, item 6.

## 4. Inspecting 43333, 5[5,6,6,6,7] and 6[6⁶] [VERIFIED]

| Hub | Dual | Ring | Classes | Direct | D-surv | B support | Wheel classes: direct / survive under D / survive under B |
|---|---|---:|---:|---:|---:|---:|---|
| 33333 | 5[6⁵] | 10 | 2,461 | 530 | 1,220 | 1,215 | 25 / 0 / 0 |
| 43333 | 5[7,6⁴] | 11 | 7,381 | 1,128 | 5,488 | 5,334 | 42 / 272 / 220 |
| 43332 | 5[7,6,6,6,5] | 10 | 2,461 | 520 | 1,320 | 1,174 | 34 / 78 / 76 |
| 43323 | 5[7,6,6,5,6] | 10 | 2,461 | 530 | 1,408 | 1,142 | 30 / 92 / 72 |
| 333333 | 6[6⁶] | 12 | 22,144 | 2,756 | 14,061 | (not run) | 116 / 327 / – |

**Containment in the RSST list.**
- Closed 5[≤6⁵] appears only in #8 = 5[5,5,6,6,6] and #12 = 5[5,6⁴].
- Closed 5[6⁴,7] appears in no RSST configuration.
- Closed 5[5,6,6,6,7] appears in three.
- Closed 6-hubs with a 5 appear in #19 and #21 (ring 11, D-reducible).
- The radius-1-like configurations that need C are #117 = 5[7,7,6,5,5] (284 remaining classes), #135 and #136 (810 each). All three use 1-edge contracts.

**Other results.**
- Every 6-hub over {5,6} with at least one 5 is D-reducible.
- 6[6⁶] is far from reducible: 63.5% of classes survive.

## 5. Question (b): what RSST discharging owes to the pockets

**RSST data.** Charge is 10(6 − deg). The rules file has 32 named rules and 67 numbered entries (35 forward entries plus 32 inversions), grouped by sender v₀:

| Rules | Entries | Sender v₀ | Role |
|---|---:|---|---|
| 1 | 2 | 5 | sends to every neighbour |
| 2–7 | 14 | 5 or 6 | six-relays: pass a 5's charge through one or two 6s to a vertex of degree ≥ 7 (rules 3–5 relay 6 → 6) |
| 8–27 | 40 | 7 | redistribute among large vertices |
| 28–32 | 11 | 8 | redistribute among large vertices |

**Proposition 5.1 [PROVED].** Under RSST rules, a degree-5 vertex v has final charge at most 2·n₅(v), where n₅(v) is its number of degree-5 neighbours.

*Proof.*
- Rule 1 ("5 59", meaning v₁ has degree 5 to ∞) and its inversion each move 1 unit from v across every incident edge. That sends out 10 in total, exhausting v's initial charge of 10.
- Every other rule has β(v₁) ≥ 6: rules 2, 6, 7 and 8–32 need v₁ ≥ 7, and rules 3–5 need v₁ ≥ 6.
- So v receives only through Rule 1, 2 units from each 5-neighbour. Rules 2 and 3 with v₀ = 5 only send more out. ∎

**Corollary 5.2.**
- 5[6⁵], 5[6⁴,7], and generally every 5-hub with no 5-neighbour, never has positive charge.
- Inside a cartwheel of a hub of degree ≥ 7, a closed 5[6⁵] cannot occur.
  - At distance 1, the hub itself is one of its neighbours and has degree ≥ 7.
  - At distance 2, the 5-vertex has neighbours outside the cartwheel, whose degrees the cartwheel does not specify.
- So adding 33333 (or the caps) to RSST changes neither the hand cases nor the computer cases. RSST spends no rule complexity on 33333. That is the honest answer to "how much complexity exists only for 5[6⁵]": none directly.

**Lemma 5.3 [PROVED] (per-edge cap).** Suppose that under some rule set, every vertex receives net charge at most τ < 10 across each edge. Then every vertex of degree d ≥ 60/(10 − τ) ends with non-positive charge.

*Proof.* The final charge is at most 10(6 − d) + τd = 60 − (10 − τ)d. ∎

RSST's ceiling of degree 11 corresponds to τ = 5, since 60/5 = 12.

**Lemma 5.4 [PROVED] (lonely-5 dilemma).** Call a 5 *lonely* if exactly one neighbour has degree ≥ 7 (m(u) = 1). Suppose charge is sent only across edges (no relays) and lonely 5s are not excluded. Then τ ≥ 10, and Lemma 5.3 gives no degree ceiling.

The lonely pockets 5[d, {5,6}⁴] have ring d + 4, so they form an infinite family. A finite reducible list cannot exclude them. The wheel already fails at d = 7 (43333: 272 wheel classes survive).

**Corollary 5.5 [PROVED, modulo reducing the pockets].** Suppose every 5 had m(u) ≥ 2. Then the direct rule "a 5 sends 10/m(u) to each neighbour of degree ≥ 7" has τ ≤ 5. That gives RSST's ceiling with no relays at all. Hence:
- **m(u) = 0 pockets.** These are 5[{5,6}⁵]. They are now excluded by caps.md plus 33333, eight radius-1 configurations.
  - As a byproduct, every triangulation with degrees in {5,6} (a fullerene dual) contains a reducible configuration.
  - IPR fullerene duals are already covered by 33333 alone.
- **m(u) = 1 pockets.** These are the lonely 5s, still open and infinite.
- The six-relay family (rules 2–7, 14 of 67 entries, about 21%) exists exactly because of these two pocket types.

The rules for v₀ = 7, 8 (51 entries) are driven by positive large hubs. They would change form but not disappear.

**[HEURISTIC] The radius does not shrink.** Under the direct rule, a 7-hub is positive iff Σ_{u ∈ N₅(v)} 1/m(u) > 1. For example, two lonely 5s make it positive. Each m(u) depends on degrees at distance 2, so positivity still needs radius-2 axles. The gain is in rule simplicity, not obviously in the number of configurations. Measuring the effect on the unavoidable set needs an automated discharging run (§9, item 3).

## 6. The convex-cone barrier

**Setup.** Let C be a configuration with ring k. A minimal counterexample's exterior vector N = N_G ∈ Z_{≥0}^{W_k} satisfies three conditions:

- **(i)** N vanishes on Dir(C).
- **(ii)** N is realizable by a planar exterior.
- **(iii)** N·c_D > 0 for every safe reducer D (Lemma 2.3).

A model F_C is any convex cone that contains every N satisfying (i) and (ii). Four models were tested:

| Model | Constraint |
|---|---|
| B | for each palette α, N = Σ y_b 1_b with y ≥ 0 over signed-matching blocks |
| L | N = Z·a lies in the BL span |
| BL | B and L together |
| D | the support closure, which is implied by B |

**Lemma 6.1 [PROVED] (cone collapse).** Let F be a convex cone and c_{D₁}, …, c_{D_r} ≥ 0. Some N ∈ F has N·c_{D_j} > 0 for all j iff for each j some N_j ∈ F has N_j·c_{D_j} > 0.

*Proof.* Take N = Σ N_j. ∎

Let M(F) be the maximal support of F. It is computed by one LP: maximise Σz subject to 0 ≤ z ≤ N, z ≤ 1, N ∈ F. Then C is reducible relative to F iff some reducer D has supp c_D ∩ M(F) = ∅. Combining reducers therefore never helps in any convex model, including every lifted or joint-palette model.

**Theorem 6.2 [VERIFIED for k = 4..9].** The intersection over α of span(signed-matching blocks of palette α) equals span{ζ_σ}. Here σ ranges over noncrossing partitions of the k-cycle in which no block contains two cyclically adjacent ring vertices. The dimension is the Riordan number R_k.

| k | Words | dim span(B_α), each α | dim ∩ | R_k = rank(BL) | Max relative residual of BL projected onto each palette span |
|---:|---:|---:|---:|---:|---:|
| 4 | 21 | 10 | 3 | 3 | 7.8e−16 |
| 5 | 60 | 25 | 6 | 6 | 1.7e−15 |
| 6 | 183 | 71 | 15 | 15 | 3.6e−15 |
| 7 | 546 | 196 | 36 | 36 | 3.6e−15 |
| 8 | 1,641 | 554 | 91 | 91 | 6.6e−15 |
| 9 | 4,920 | 1,569 | 232 | 232 | 7.0e−15 |

*Proof status.*
- The inclusion BL ⊆ ∩_α span(B_α) is numerically exact for k ≤ 9. For realizable vectors it is also immediate: Kempe chains split the colourings of one exterior into α-blocks, and Birkhoff–Lewis places N_G in the BL span.
- The reverse inclusion is the new fact: Kempe linear relations cut out exactly the BL space. Here it is verified by equal dimensions. Together these give equality for k ≤ 9; for general k it is a conjecture.

**Corollary 6.3 [PROVED given 6.2].** Every N feasible for B lies in each palette span, hence in BL. So adding BL constraints to B changes nothing. The data agree: the B and BL max supports were identical labelled sets on all 73 hubs (rings 5–10). The same holds at ring 11 on 43333 (32,004 labelled words, 5,334 classes), where rank(BL) = 1,585 = R₁₁. Theorem 6.2 itself was not checked at k = 11, so this is supporting evidence rather than a verification.

### 6.4 LP experiments [VERIFIED]

Rows are the hubs with D-survivors. All support sizes are classes modulo S₃. "B removes" is the fraction of D-survivors outside the B support. The disk column counts passing disks with at most one interior vertex, out of N such disks at that ring.

| Hub | Dual | Ring | D-surv | B | L | BL | B removes | Passing disks, ≤1 interior vertex (D / B, of N) | Wheel∩D / Wheel∩B (classes) |
|---|---|---:|---:|---:|---:|---:|---:|---|---|
| 52222 | 5[8,5,5,5,5] | 8 | 100 | 100 | 178 | 100 | 0.0% | 51/51 of 1,419 | 0 / 0 |
| 42422 | 5[7,5,7,5,5] | 9 | 376 | 364 | 536 | 364 | 3.2% | 0/0 of 5,434 | 24 / 24 |
| 43322 | 5[7,6,6,5,5] | 9 | 356 | 356 | 438 | 356 | 0.0% | 0/0 of 5,434 | 32 / 32 |
| 43223 | 5[7,6,5,5,6] | 9 | 352 | 352 | 440 | 352 | 0.0% | 0/0 of 5,434 | 30 / 30 |
| 44222 | 5[7,7,5,5,5] | 9 | 320 | 320 | 556 | 320 | 0.0% | 86/86 of 5,434 | 48 / 48 |
| 522222 | 6[8,5,5,5,5,5] | 9 | 305 | 305 | 305 | 305 | 0.0% | 168/168 of 5,434 | 0 / 0 |
| 52322 | 5[8,5,6,5,5] | 9 | 305 | 305 | 460 | 305 | 0.0% | 168/168 of 5,434 | 0 / 0 |
| 53222 | 5[8,6,5,5,5] | 9 | 305 | 305 | 564 | 305 | 0.0% | 168/168 of 5,434 | 0 / 0 |
| 43422 | 5[7,6,7,5,5] | 10 | 1,698 | 1,662 | 1,879 | 1,662 | 2.1% | 0/0 of 20,878 | 100 / 96 |
| 44322 | 5[7,7,6,5,5] | 10 | 1,664 | 1,652 | 1,850 | 1,652 | 0.7% | 0/0 of 20,878 | 122 / 122 |
| 52422 | 5[8,5,7,5,5] | 10 | 1,660 | 1,628 | 1,922 | 1,628 | 1.9% | 0/0 of 20,878 | 56 / 56 |
| 53322 | 5[8,6,6,5,5] | 10 | 1,605 | 1,605 | 1,772 | 1,605 | 0.0% | 0/0 of 20,878 | 75 / 75 |
| 53223 | 5[8,6,5,5,6] | 10 | 1,588 | 1,588 | 1,765 | 1,588 | 0.0% | 0/0 of 20,878 | 70 / 70 |
| 54222 | 5[8,7,5,5,5] | 10 | 1,538 | 1,538 | 1,973 | 1,538 | 0.0% | 57/57 of 20,878 | 112 / 112 |
| 43323 | 5[7,6,6,5,6] | 10 | 1,408 | 1,142 | 1,385 | 1,142 | 18.9% | 0/0 of 20,878 | 92 / 72 |
| 43332 | 5[7,6,6,6,5] | 10 | 1,320 | 1,174 | 1,371 | 1,174 | 11.1% | 0/0 of 20,878 | 78 / 76 |
| 43242 | 5[7,6,5,7,5] | 10 | 1,312 | 1,228 | 1,635 | 1,228 | 6.4% | 0/0 of 20,878 | 56 / 56 |
| 33333 | 5[6,6,6,6,6] | 10 | 1,220 | 1,215 | 1,701 | 1,215 | 0.4% | 1/1 of 20,878 | 0 / 0 |
| 422422 | 6[7,5,5,7,5,5] | 10 | 1,182 | 1,094 | 1,378 | 1,094 | 7.4% | 0/0 of 20,878 | 88 / 88 |
| 442222 | 6[7,7,5,5,5,5] | 10 | 976 | 976 | 1,018 | 976 | 0.0% | 259/259 of 20,878 | 96 / 96 |
| 44232 | 5[7,7,5,6,5] | 10 | 976 | 976 | 1,466 | 976 | 0.0% | 259/259 of 20,878 | 96 / 96 |
| 522322 | 6[8,5,5,6,5,5] | 10 | 910 | 910 | 910 | 910 | 0.0% | 582/582 of 20,878 | 0 / 0 |
| 523222 | 6[8,5,6,5,5,5] | 10 | 910 | 910 | 1,150 | 910 | 0.0% | 582/582 of 20,878 | 0 / 0 |
| 52332 | 5[8,5,6,6,5] | 10 | 910 | 910 | 1,386 | 910 | 0.0% | 582/582 of 20,878 | 0 / 0 |
| 532222 | 6[8,6,5,5,5,5] | 10 | 910 | 910 | 910 | 910 | 0.0% | 582/582 of 20,878 | 0 / 0 |
| 53232 | 5[8,6,5,6,5] | 10 | 910 | 910 | 1,428 | 910 | 0.0% | 582/582 of 20,878 | 0 / 0 |
| 43333 | 5[7,6,6,6,6] | 11 | 5,488 | 5,334 | 6,019 | 5,334 | 2.8% | not run (k = 11) | 272 / 220 |

**Findings.**
1. B ⊆ D on all 73 hubs and on 43333, as it must be, since the D-closure is implied by the block equations.
2. B is strictly stronger than D on 9 of the 26 hubs, by 0.4% (33333) up to 18.9% (43323). The largest gains are on the two 5[5,6,6,6,7] embeddings: 18.9% and 11.1%.
3. L alone allows more classes than D in 22 hubs and the same number in 3. It allows fewer only for 43323, with 1,385 classes against 1,408. For 33333 it allows 1,701 classes against 1,220.
4. No disk with at most one interior vertex passes under B unless it already passes under D.
5. B lowers the wheel's survivor overlap in only three hubs at rings 8–10: 43422 (100 to 96), 43332 (78 to 76) and 43323 (92 to 72). At ring 11 it lowers 43333 from 272 to 220 of 341 wheel classes. It never reaches 0, so the wheel fails under B wherever it failed under D.

## 7. Breaking the barrier: non-convex invariants (assessment)

Theorem 6.2 says the known linear identities for planar exteriors (Birkhoff–Lewis) are already implied by the Kempe block equations. Lemma 6.1 says any convex model, however fine, can only sharpen the single-reducer test. Any gain from combining reducers therefore needs non-convex information.

- **N1. Joint-palette lift [PROPOSAL].**
  - One variable per consistent triple (b₁, b₂, b₃) of α-blocks containing the same colouring.
  - Strictly finer than B, but still a cone, so it only strengthens single reducers. It has not been measured yet; see §9, item 4.
- **N2. Realizability, the only route to multi-reducer gains.**
  - Look for a pair of reducers D₁, D₂ for C with two properties. Each single LP fails, yet no single planar exterior has words in both supp c_{D₁} and supp c_{D₂} while avoiding Dir(C).
  - Such a pair would be a genuine non-convex certificate.
  - The natural tool is cross-palette planarity of Kempe chains: α-chains (colours β, γ) and β-chains (colours α, γ) share γ-edges, so the three matchings of one colouring are correlated. This is in the spirit of Tilley's Kempe-locking analysis.
- **N3. Algebraic identities.**
  - Tutte's golden identity is quadratic, but it links Q = φ + 1 and Q = φ + 2, not Q = 4.
  - Theorem 6.2 shows that Kempe chains impose no linear relation beyond BL. A further linear identity would need a source other than Kempe chains. Q = 4 is not a Beraha number, so no Temperley–Lieb degeneracy is expected there [HEURISTIC].
  - No quadratic identity at Q = 4 is known. Without one, this route does not produce a constraint.
- **N4. Multiple configurations in one counterexample.**
  - A minimal counterexample contains many configurations, and their overlapping exteriors are coupled.
  - The coupling is non-convex and unexplored.
  - It is the only mechanism that could turn "many weak local facts" into a proof with fewer configurations.

## 8. The fundamental obstruction: why hundreds of configurations

1. **Curvature dilution [classical].** Σ(6 − deg) = 12 lets positive curvature be arbitrarily sparse in a hexagonal sea. Discharging must therefore match every local surplus to an exact, rigid degree pattern. Reducibility is fragile under single degree changes. 33333 reduces, but the wheel fails on 43333 and 43332, and 43332 has no passing disk with at most one interior vertex.
2. **Per-configuration power is about D [VERIFIED].** Lemma 6.1 plus Theorem 6.2 show that adding BL linear relations, or combining reducers, cannot improve on the B-LP. B adds at most 18.9% over D in the samples, and it turned no failing disk into a passing one.
3. **Decay at fixed interior [VERIFIED].** For radius-1 5-caps:

   | Ring | Survivor fraction | Direct fraction |
   |---:|---:|---:|
   | 10 | 49.6% | 21.5% |
   | 11 | 74.4% | 15.3% |
   | 12 | 86.1% | 10.5% |
   | 13 | 90.4% | 7.1% |
   | 14 | 94.0% | 4.8% |

   The direct fraction falls by a factor of about 0.69 per ring vertex. Reducible configurations must therefore grow their interior roughly linearly with their ring, which is Heesch's observation.
4. **Discharging trade-off [PROVED, Lemmas 5.3 and 5.4].** Lonely 5s force a choice. Either a relay rule makes charge travel distance 2, which needs radius-2 cartwheels, rings 12–14 and survivor fractions of 86–94%; this is RSST's choice, with 506 of 633 configurations at rings 12–14. Or concentrated sending leaves an infinite family with no degree ceiling.
5. **Synthesis [HEURISTIC].** The configuration count is roughly the number of positive radius-2 degree patterns at hubs of degree 7–11, divided by how much reducible witnesses can share. Each witness is rigid and needs ring ≥ 12 to be reducible.
6. **What could change the order of magnitude.** One of three things:
   - a parametric reduction of the lonely-5 family 5[d,{5,6}⁴] (removing the relays);
   - a non-convex multi-reducer certificate (N2);
   - cross-configuration coupling (N4).

## 9. Phase 3 handoff for gpt-6.2-astra

1. **Prove Theorem 6.2 for all k.**
   - Find a closed form for the palette span dimensions 10, 25, 71, 196, 554, 1,569 (k = 4..9).
   - Identify each palette span as a chromatic or Temperley–Lieb-type module whose triple intersection is the Riordan-dimensional BL module.
2. **Attack the lonely-5 family 5[d,6⁴], ring d + 4.**
   - Start at d = 7 (43333). The targets are the B-support (5,334 classes) and disks with 2–4 interior vertices.
   - Look for a uniform-in-d reducer; the wheel fails.
   - A positive result removes the six-relay rules (Corollary 5.5).
3. **Run automated discharging.** Use Steinberger's L₄₂ pipeline (arXiv:0905.0043 ancillary files). Replace RSST rules 1–7 with the direct rule. Add caps.md plus 33333 as reducible, and treat the lonely-5 pockets as reducible. Measure the resulting unavoidable set size. That is the payoff available if item 2 succeeds.
4. **Run the joint-palette lifted LP (N1).** Targets are 43333, 43332, 43323 and 42422. Report the support shrinkage beyond B and whether any disk with at most one interior vertex starts to pass.
5. **Search for realizability counterexamples (N2).** For 43333, take the two best partial-wheel reducers. Search exteriors (plantri with outer ring 11, fullerene-like exteriors) for one realizing words in both reducer supports while avoiding Dir(C). If none appear up to size n, attempt a proof by Kempe chain planarity.
6. **Find a human proof of the 33333 wheel fact.** Show that every ring colouring missing a colour is Kempe-certified. The machine certificate has 826 classes and depth 13; try to compress it using D₅ symmetry and the m-stratification of §3.

## 10. Reproducibility

The scratchpad is session-temporary. Copy anything worth keeping.

- **Native D-process probe:** `gprobe.cpp`. Run `./gprobe GAPS out.txt`.
- **Hub outputs:** `hubs/*.txt`.
- **Wheel checks:** `wov.py` (wheel versus D-survivor overlap) and `wheel_lp.py` (wheel versus LP supports).
- **Kempe analysis:**
  - `kempe.py` covers restricted closure.
  - `ancestry.py` builds the ancestral certificate.
  - `mult.py` and `winding.py` compute the multiplicity and winding tables.
- **LPs:**
  - `lp.py` contains the B, L and BL max-support code.
  - `run_lp.py` runs them; `batch_lp.sh` runs the whole hub batch.
  - `evalred.py` scores disks with at most one interior vertex.
  - `reducers.py` enumerates the disks.
  - Logs are in `batch_lp.log` and `lp43333.log`.
- **Theorem 6.2 checks:** `spans3.py` (k = 9 log: `spans3_9.log`).
- **Final table:** `final_table.py`, output `final_table.md`. `setcheck.py` checks B = BL as labelled sets. `b43333.py` gives the 43333 wheel∩B count; the 43333 run log is `lp43333.log` (BL took 913 s).

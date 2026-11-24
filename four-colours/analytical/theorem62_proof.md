# Theorem 6.2 for all k: the Kempe spans cut out exactly the Birkhoff–Lewis span

*Phase 4B, analytical thrust. This file is a self-contained proof. Each lemma is tagged **[PROVED]** or **[CONJECTURED]**, and statements quoted from the literature are tagged by how they were checked. The sanity script is `theorem62_check.py` in this directory (single-threaded, k ≤ 9, about 3.5 s).*

---

## 0. Results

Fix a ring size k ≥ 2. Let W_k be the set of Tait words t ∈ {1,2,3}^k with t_1 ⊕ … ⊕ t_k = 0. Letters are identified with F₂² ∖ {0}: 1 = (1,0), 2 = (0,1), 3 = (1,1).

- B_α ⊆ ℝ^{W_k} is the span of the indicators of the signed noncrossing-matching (Kempe) blocks of palette α ∈ {1,2,3}. See §1.
- BL_k = span{ζ_σ}, where σ ranges over 𝓡_k, the noncrossing partitions of the k-cycle with no two cyclically adjacent ring vertices in a block. Here ζ_σ(t) = [the ring colouring c(t) is constant on every block of σ].

**Theorem A [PROVED].** For every k ≥ 2 and every pair of distinct palettes α ≠ β,

  B_α ∩ B_β = BL_k,  and hence  B_1 ∩ B_2 ∩ B_3 = BL_k.

Moreover dim BL_k = R_k, the Riordan number (OEIS A005043): 1, 1, 3, 6, 15, 36, 91, 232, 603, 1585, … for k = 2, 3, …

Two palettes already suffice. The third palette adds no further linear relation.

**Theorem B [PROVED] (closed form).** Let T_k = Σ_m C(k,2m)·C(2m,m) be the central trinomial coefficient. Then

  dim B_α = Σ_{m≥1} C(k,2m)·C(2m,m)/2 + [k even] = (T_k + (−1)^k)/2.

The generating function is

  Σ_k dim B_α · x^k = ½·( 1/√((1+x)(1−3x)) + 1/(1+x) ).

| k | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| T_k | 3 | 7 | 19 | 51 | 141 | 393 | 1107 | 3139 | 8953 | 25653 | 73789 |
| dim B_α | 2 | **3** | 10 | 25 | 71 | 196 | 554 | 1569 | **4477** | 12826 | 36895 |
| R_k = dim BL_k | 1 | 1 | 3 | 6 | 15 | 36 | 91 | 232 | 603 | 1585 | 4213 |

T_k satisfies k·T_k = (2k−1)·T_{k−1} + 3(k−1)·T_{k−2} and T_k ~ 3^{k+1/2}/(2√(πk)). The dimension sequence 2, 3, 10, 25, 71, … did not match any OEIS entry I searched for.

For comparison, the Riordan numbers have generating function (1 + x − √((1+x)(1−3x)))/(2x(1+x)). The same square root therefore governs both sides.

**Proof architecture.**

1. Each B_α is described as a Fourier-support condition (balanced sets; Lemma 2).
2. The problem is lifted from words to free functions f(a,b) of 4-colourings c = (a,b) ∈ (F₂²)^V. There the two palettes become the conditions "f(·,b) is a free a-Kempe function for every b" and the same with a and b swapped.
3. In the free setting the intersection equals the span 𝔏 of the noncrossing-partition indicators α_σ, for every k (Theorem 5.1). The proof is an induction on k using two operators that preserve everything: averaging a vertex colour and contracting an edge.
4. The inductive step reduces to an uncertainty lemma. A word function that is antisymmetric/sum-free under every local Kempe move and lies in B_1 ∩ B_2 must vanish. Its proof is a Krawtchouk-polynomial computation.
5. Restricting the free identity to proper colourings gives Theorem A. Independence of the α_σ (needed for dim = R_k) is proved via Rumer vectors.

---

## 1. Setup and notation

- **Ring vertices and words.** Ring vertices are V = ℤ_k = {0, …, k−1}, in cyclic order. A colouring is c ∈ (F₂²)^V, written c_v = (a_v, b_v), with a, b ∈ F₂^V. Following the memo, the letter t_j (j = 1..k) sits on the edge {j−1, j} and equals c_j ⊕ c_{j−1}. Letter 1 means "a flips, b stays", 2 means "b flips, a stays", 3 means "both flip".
  - c is proper (c_{j−1} ≠ c_j for all j) iff t(c) ∈ W_k.
  - Proper colourings modulo translation c ↦ c + x (x ∈ F₂²) are in bijection with W_k. The memo normalisation is c_0 = 0, c_j = t_1 ⊕ … ⊕ t_j.
- **ζ_σ.** For a partition σ of V, ζ_σ(t) = [c(t) constant on each block of σ]. This is well defined because the condition is translation invariant.
- **Sectors.** Fix a palette α and let β, γ be the other two letters, so β ⊕ γ = α. The α-sector of a word is S = {j : t_j ≠ α}.
  - Projecting the condition Σt = 0 to F₂²/⟨α⟩ shows |S| = 2m is even.
  - On a sector write y_j = [t_j = γ] for j ∈ S. Then t_j = β ⊕ y_j·α. Σt = 0 becomes Σ_{j∈S} y_j ≡ k (mod 2), so y ranges over the affine hyperplane H_S = {y ∈ F₂^S : |y| ≡ k}.
  - The sector has 2^{2m−1} words when m ≥ 1. For S = ∅ it is the single word α^k, which exists iff k is even.
- **Kempe blocks** (the memo's "signed-matching blocks"). Let M be a noncrossing (NC) perfect matching of S, noncrossing for the cyclic order of positions. Let t be a word in the sector. The block 𝔟(t, M) is the set of words obtained from t by switching β ↔ γ at both ends of any subset of the pairs of M. This is the literal Kempe switch of the chains realising M.
  - In y-coordinates, 𝔟(t, M) = y(t) + V_M with V_M = span{e_a + e_b : {a,b} ∈ M}.
  - B_α is the span of all the 1_𝔟. Every block lies inside one sector.
- **Balanced sets.** List a cyclically ordered set S of size 2m as s_1, …, s_{2m}. U ⊆ S is balanced if Σ_{s_i∈U} (−1)^i = 0. Changing the starting point of the list multiplies every sign by −1, so the notion is cyclic. U is balanced iff S∖U is balanced.
- **Characters.** χ_U(y) = (−1)^{Σ_{j∈U} y_j}.

---

## 2. The palette spans (Lemma 2) and the closed form

**Lemma 2.1 [PROVED] (balanced lemma).** Let S = {s_1 < … < s_{2m}} and U ⊆ S. Then U is a union of pairs of some NC perfect matching of S iff U is balanced.

*Proof.*
- (⇒) In an NC perfect matching, a pair {s_i, s_j} with i < j encloses s_{i+1}, …, s_{j−1}, which are matched among themselves. So j − i is odd and the pair contributes (−1)^i + (−1)^j = 0.
- (⇐) Induct on m. The case m = 0 is trivial. Write u_i = [s_i ∈ U].
  - If some cyclically consecutive u_i = u_{i+1}, match s_i with s_{i+1} and delete both. The deleted pair contributes 0 to the charge, and later indices shift by 2, so the remaining set is still balanced.
  - By induction the remaining 2m − 2 points have an NC matching whose pairs lie inside U or inside S∖U. Adding the adjacent pair {s_i, s_{i+1}} keeps it noncrossing.
  - If no two consecutive u_i are equal, u alternates and the charge is ±m ≠ 0, which is impossible. ∎

**Lemma 2.2 [PROVED] (Kempe characterisation).** For each sector S,

  B_α|_S = span{χ_U|_{H_S} : U ⊆ S balanced},  and  B_α = ⊕_S B_α|_S.

Equivalently, a function F on the sector lies in B_α iff the Fourier transform of its zero-extension to F₂^S is supported on balanced sets.

*Proof.*
- The indicators of the cosets of V_M inside H_S span the V_M-invariant functions on H_S. These are the span of the χ_U|_H with χ_U trivial on V_M.
- χ_U is trivial on V_M iff |U ∩ {a,b}| is even for every pair of M, i.e. iff U is a union of pairs of M.
- Taking the union over M and applying Lemma 2.1 gives the first claim.
- For the second claim, use 1_H = (1 + (−1)^k χ_S)/2. The zero-extension of χ_U|_H is then (χ_U + (−1)^k χ_{S∖U})/2. U is balanced iff S∖U is.
- Conversely, a function supported on H whose Fourier support is balanced is a combination of balanced χ_U, and restricting it to H gives the same function. ∎

**Proof of Theorem B [PROVED].**
- On H the characters χ_U and χ_{S∖U} agree up to sign, and χ_U|_H for U in a system of representatives of {U, S∖U} form an orthogonal basis.
- For m ≥ 1, S has C(2m,m) balanced subsets: Σ_j C(m,j)², counting equal numbers of odd- and even-indexed elements. They fall into C(2m,m)/2 complement pairs, since U ≠ S∖U.
- The sector S = ∅ (k even) contributes 1.
- There are C(k,2m) sectors of size 2m, so dim B_α = Σ_{m≥1} C(k,2m)C(2m,m)/2 + [k even] = (T_k − 1)/2 + [k even] = (T_k + (−1)^k)/2.
- The generating function follows from Σ T_k x^k = (1 − 2x − 3x²)^{−1/2}. The recurrence and asymptotics are the standard ones for T_k. ∎

---

## 3. The free setting

From here on, V is any finite cyclically ordered set with |V| = k ≥ 1. "Adjacent" means consecutive in the cyclic order; for k = 2 the two vertices are adjacent. Functions are f : (F₂²)^V → ℝ, written f(a, b), with inner product ⟨f, g⟩ = Σ_c f(c)g(c).

- For a partition π of V and x ∈ F₂^V, α_π(x) = [x is constant on every block of π]. For colourings, α_σ(c) = α_σ(a)·α_σ(b).
- For b ∈ F₂^V, write ker b for the partition of V into {b = 0} and {b = 1}.
- Y ⊆ V is **b-matchable** if Y has an NC perfect matching whose pairs join vertices with equal b. By Lemma 2.1 this holds iff |Y| is even and Y ∩ b^{−1}(1) is balanced in Y.

**Definitions.**

- 𝒜(b) = span{α_π(a) : π ∈ NC(V), π ≤ ker b}. This is a space of functions of a.
- 𝔅_1 = {f : f(·, b) ∈ 𝒜(b) for all b} = span{[b = b_0]·α_π(a) : π NC, π ≤ ker b_0}.
- 𝔅_2 is defined the same way with the roles of a and b swapped.
- 𝔏 = span{α_σ(c) : σ ∈ NC(V)}.
- X = 𝔅_1 ∩ 𝔅_2.

*Interpretation.* 𝔅_1 is the free version of palette-1 Kempe consistency. The b-level sets split into face-Kempe regions π, and switching a on any region is allowed.

**Lemma 3.1 [PROVED] (Fourier form of 𝒜(b)).** 𝒜(b) = span{χ_Y(a) : Y b-matchable}.

*Proof.*
- (⊆) α_π = Π_B [a const on B] = 2^{|π|−k} Σ_Y χ_Y, where Y ranges over sets meeting every block of π in an even number of points. Pair the points of Y ∩ B consecutively inside each block B. This gives an NC matching, because π is NC, and its pairs have equal b, because π ≤ ker b.
- (⊇) Let M be an NC matching of Y with b-equal pairs. Then χ_Y(a) = Π_{{u,v}∈M} (2[a_u = a_v] − 1) = Σ_{M'⊆M} (−1)^{|M∖M'|} 2^{|M'|} α_{π_{M'}}(a).
  - Here π_{M'} has the pairs of M' as blocks and singletons elsewhere. It is NC and satisfies π_{M'} ≤ ker b. ∎

**Corollary 3.2 [PROVED].**

1. Every f ∈ 𝔅_1 satisfies f(a+1, b) = f(a, b), since every b-matchable Y has |Y| even. Similarly every f ∈ 𝔅_2 satisfies f(a, b+1) = f(a, b). Hence X is invariant under all translations c ↦ c + x.
2. dim 𝔅_1 = Σ_b #{Y : Y b-matchable} = Σ_j C(k,2j)·C(2j,j)·2^{k−2j} = C(2k,k). The last equality is [x^k](1 + 2x + x²)^k.
3. 𝔏 ⊆ X. For fixed b, α_σ(a)α_σ(b) is either 0 or α_σ(a) with σ ≤ ker b; the same holds with a and b swapped.

**Lemma 3.3 [PROVED] (merging lemma).** Let π ∈ NC(V) and let v, w be adjacent. Then π ∨ {v, w} ∈ NC(V).

*Proof.*
- Suppose the merged block B_v ∪ B_w crossed another block C.
- Two disjoint blocks do not cross iff one lies in a single gap of the other, where a gap is a maximal arc of V ∖ C.
- B_v lies in one gap of C, and so does B_w. These gaps must differ.
- But v and w are adjacent and both outside C, so they lie in the same gap. Contradiction. ∎

**Operators.**
- E_v f = ¼ Σ_{x∈F₂²} f(c with c_v := x) averages over the colour of vertex v.
- For adjacent v, w, Q_{vw} f = [c_v = c_w]·f.

**Lemma 3.4 [PROVED].** E_v and Q_{vw} preserve 𝔅_1, 𝔅_2 and 𝔏. Both are self-adjoint.

*Proof.*
- **E_v on 𝔅_1.** Averaging over a_v keeps exactly the characters χ_Y with v ∉ Y. Such a Y is b-matchable for one value of b_v iff it is for the other.
- **Q_{vw} on 𝔅_1.** For fixed b, Q_{vw} f(·, b) is 0 if b_v ≠ b_w. Otherwise it equals [a_v = a_w]·f(·, b), and [a_v = a_w]α_π = α_{π∨vw} with π∨vw NC (Lemma 3.3) and ≤ ker b.
- **On 𝔏.** E_v α_σ = ¼ α_{σ'}, where σ' splits v off its block (or E_v α_σ = α_σ if v is already a singleton). Q_{vw} α_σ = α_{σ∨vw}.
- 𝔅_2 is handled by the symmetric argument. ∎

**Lemma 3.5 [PROVED] (restriction).** Let g ∈ X(V) ∩ 𝔏(V)^⊥ be independent of c_v, and let g̃ be g viewed as a function on (F₂²)^{V∖v}. Then g̃ ∈ X(V∖v) ∩ 𝔏(V∖v)^⊥.

*Proof.*
- g(·, b) has Fourier support in the b-matchable Y with v ∉ Y. These are exactly the b|_{V∖v}-matchable subsets of V∖v in the induced cyclic order. The same argument applies to 𝔅_2.
- For σ' ∈ NC(V∖v), let σ = σ' ∪ {{v}} ∈ NC(V). Then α_σ(c) = α_{σ'}(c|_{V∖v}), so ⟨g, α_σ⟩_V = 4⟨g̃, α_{σ'}⟩_{V∖v}. ∎

**Lemma 3.6 [PROVED] (contraction).** Let v, w be adjacent, let V/e be V with v and w merged into one vertex (induced cyclic order), and let f_e be the restriction of f to {c_v = c_w}, viewed on (F₂²)^{V/e}. If f ∈ X(V) ∩ 𝔏(V)^⊥, then f_e ∈ X(V/e) ∩ 𝔏(V/e)^⊥.

*Proof.*
- Take b with b_v = b_w and write f(·, b) = Σ λ_π α_π(a) over NC π ≤ ker b.
- On a_v = a_w we have α_π = α_{π∨vw}. After contraction this is α_{π̄}, where π̄ is NC (Lemma 3.3, then contract two adjacent points of one block) and π̄ ≤ ker b̄. The same argument applies to 𝔅_2.
- For σ̄ ∈ NC(V/e), let σ be its lift with v, w in one block. σ is NC because v, w are adjacent. Then α_σ(c) = [c_v = c_w]·α_{σ̄}(c̄), so ⟨f_e, α_{σ̄}⟩ = ⟨f, α_σ⟩ = 0. ∎

---

## 4. From free functions back to words

Throughout this section f is supported on proper colourings and is translation invariant. Equivalently, f = F∘t for a unique F : W_k → ℝ, with f = 0 off proper colourings. Let τ be the coordinate swap (a,b) ↦ (b,a). On letters, τ swaps 1 and 2 and fixes 3.

**Lemma 4.1 [PROVED] (link lemma).** f ∈ 𝔅_1 iff F ∈ B_1. Likewise f ∈ 𝔅_2 iff F ∈ B_2.

*Proof.* Fix b and set g_b = f(·, b).

*Constant b.* Proper colourings force a to alternate around the ring, so k is even and the word is 1^k. Every Y of even size is b-matchable, so 𝒜(b) = {functions invariant under a ↦ a+1}, and g_b has this invariance. The palette-1 sector of 1^k is S = ∅, where B_1 imposes nothing either. Neither side has a condition.

*Non-constant b.*
- **Runs and phases.** Let s_1 < … < s_{2m} (m ≥ 1) be the positions where b flips. These are exactly the palette-1 sector S of every word with this b. Let R_i be the run of vertices [s_i, s_{i+1} − 1] (cyclically), on which b is constant.
  - Properness forces a to alternate inside every run, so a = a(ã) is determined by the phases ã_i = a_{s_i} ∈ F₂, i ∈ ℤ_{2m}. The set A_b of such a is an affine space of dimension 2m.
  - Put G_b(ã) = g_b(a(ã)).
- **Characters on A_b.** For a ∈ A_b, χ_Y(a) = ±χ_{Ỹ}(ã) with Ỹ = {i : |Y ∩ R_i| odd}. Since g_b vanishes off A_b, ĝ_b(Y) = 2^{2m−k}·(±1)·Ĝ_b(Ỹ). Every Z ⊆ ℤ_{2m} is some Ỹ.
  - Hence g_b ∈ 𝒜(b) iff Ĝ_b(Z) ≠ 0 implies every Y with Ỹ = Z is b-matchable.
- **Reduction to runs.** Points of Y inside one run are consecutive in Y and carry equal b. Deleting two such consecutive points preserves |Y| mod 2, Ỹ, and the charge of Y ∩ b^{−1}(1) (the argument of Lemma 2.1).
  - After reduction Y has at most one point per run and is order-isomorphic to Ỹ, with b-values equal to the run colours. Run colours alternate with i.
  - So Y is b-matchable iff Ỹ is *run-matchable*: it has an NC matching joining runs of equal parity, i.e. |Ỹ| is even and Σ_l (−1)^l [ỹ_l odd] = 0 over Ỹ = {ỹ_1 < …}.
- **The words.** Off S every letter is 1. At s_i, with y_j = [t_j = 3] (a flips), we get y_{s_i} = ã_i + ã_{i−1} + |R_{i−1}| − 1.
  - So ã ↦ y is an affine surjection F₂^{2m} → H_S with kernel {0, 𝟙} (global a-flip), and G_b = F|_S ∘ y.
  - For U ⊆ S, χ_U(y(ã)) = ±χ_{∂U}(ã) with ∂U = {i : [s_i ∈ U] ≠ [s_{i+1} ∈ U]}. The map U ↦ ∂U is a bijection from complement pairs {U, S∖U} onto the even subsets of ℤ_{2m}.
  - Writing F|_S = Σ_{U∈𝒰} d_U χ_U|_H over representatives 𝒰 gives Ĝ_b(∂U) = ±d_U.
- **Balanced versus run-matchable.** It remains to show U is balanced iff ∂U is run-matchable.
  - If u_i = [s_i ∈ U] alternates, then U is unbalanced (charge ±m) and ∂U = ℤ_{2m} is not run-matchable (charge −m). So assume otherwise.
  - Rotate the indexing, which changes neither notion, so that u_{2m} = u_1. Replace U by S∖U if needed so that u_{2m} = u_1 = 0. Then ∂U = {i_1 < … < i_{2r}} ⊆ [1, 2m−1] and U = ∪_l [i_{2l−1}+1, i_{2l}].
  - Using Σ_{i=p+1}^{q} (−1)^i = ((−1)^q − (−1)^p)/2,

    charge(U) = ½ Σ_{l=1}^{2r} (−1)^l (−1)^{i_l} = −Σ_l (−1)^l [i_l odd],

    which is minus the run charge of ∂U.
  - So B_1 on sector S (Lemma 2.2: d_U = 0 for unbalanced U) is equivalent to g_b ∈ 𝒜(b).
- **All sectors.** Each nonempty even S arises from exactly two b (b and b + 𝟙), which proves the palette-1 statement.

*Palette 2.* B_2 = {F : F∘τ ∈ B_1}, because τ maps palette-1 Kempe blocks onto palette-2 blocks. Also 𝔅_2 = {f : f∘τ ∈ 𝔅_1}, and f∘τ = (F∘τ)∘t. ∎

**Lemma 4.2 [PROVED] (local Kempe conditions).** E_v f = 0 for all v ∈ V iff F ∈ N_k. Here N_k is the set of F satisfying, at every pair of cyclically adjacent positions (j, j+1), including (k, 1), and for every context:

- **(A)** F(…pq…) = −F(…qp…) for distinct letters p ≠ q;
- **(S)** F(…11…) + F(…22…) + F(…33…) = 0.

*Proof.*
- Vertex v lies between positions v and v+1. Changing c_v to x keeps s = t_v ⊕ t_{v+1} = c_{v−1} ⊕ c_{v+1} fixed, and the colourings that remain proper are those with x ∉ {c_{v−1}, c_{v+1}}.
- If s ≠ 0, the two admissible x give the letter pairs (p, q) and (q, p), where {p, q} = {1,2,3} ∖ {s}.
- If s = 0, the three admissible x give (r, r) for r = 1, 2, 3.
- So E_v f = 0 says exactly (A) or (S) at that pair. ∎

**Lemma 4.3 [PROVED] (solving the local conditions).** Let inv(w) be the number of inversions of w for the order 1 < 2 < 3, and let n(w) = (n_1, n_2, n_3) be the content of w. Then F ∈ N_k iff

  F(w) = (−1)^{inv(w)}·g(n(w)),  with  Σ_{r=1}^{3} g(ν + 2e_r) = 0 for every admissible content ν of length k − 2.

A content is admissible iff n_1 ≡ n_2 ≡ n_3 (mod 2). This is exactly the condition Σt = 0.

*Proof.*
- **(A) at linear pairs.** An adjacent swap of distinct letters changes inv by ±1. Bubble sort connects all words of a given content, so (A) at the linear pairs is equivalent to the displayed form.
- **(A) at the cyclic pair.** Swapping t_1 = p and t_k = q changes inv by 1 + n_p(u) + n_q(u) (mod 2), where u is the middle part. Admissibility makes n_p(u) + n_q(u) ≡ n_p + n_q ≡ 0, so the change is odd and (A) holds automatically.
- **(S) at a linear pair.** inv(u rr u') ≡ inv(uu'), because the letters rr create inversions in pairs. So (S) reads (−1)^{inv(uu')} Σ_r g(n(uu') + 2e_r) = 0.
- **(S) at the cyclic pair.** inv(r u r) = inv(u) + (k − 2) − n_r(u) ≡ inv(u), because every n_r(u) ≡ k (mod 2).
- Every admissible ν of length k − 2 occurs as such a context. ∎

*Remark [PROVED].* dim N_k = K + 1 for k = 2K, and (k−1)/2 for k odd. The constraint map is adjoint to multiplication by x_1 + x_2 + x_3 between spaces of homogeneous polynomials, which is injective. So the constraints are independent, and the dimension is C(K+2,2) − C(K+1,2) (k even) or C(L+2,2) − C(L+1,2) with L = (k−3)/2 (k odd). This remark is not used below.

**Lemma 4.4 [PROVED] (uncertainty lemma).** For every k ≥ 2, N_k ∩ B_1 ∩ B_2 = 0.

*Proof.* Let F = (−1)^{inv}·g(n) lie in B_1. Fix a palette-1 sector S = {s_1 < … < s_{2m}} with m ≥ 1, and use the coordinates y_l = [t_{s_l} = 3] ∈ F₂^{2m}.

1. **Sign in sector coordinates.** Inversions with a letter 1 contribute a constant inv_0(S). Inside S the count is inv(y) = #{l < l' : y_l = 1, y_{l'} = 0} ≡ Σ_l l·y_l + C(|y|, 2) (mod 2). Hence

   F|_S(y) = ε_S·χ_O(y)·φ(|y|),  with  φ(h) = (−1)^{C(h,2)}·g(k−2m, 2m−h, h).

   Here O = {s_l : l odd}, and φ(h) := 0 for h ≢ k (zero-extension).
2. **Krawtchouk step.** By Lemma 2.2, F|_S ∈ B_1 iff the Fourier transform of Φ(y) = φ(|y|), shifted by O, is supported on balanced U.
   - U is balanced iff |U △ O| = (m − |U∩O|) + |U∩E| = m, where E = S ∖ O.
   - Φ is symmetric, so Φ̂(W) depends only on |W|. The condition is therefore Φ̂ = λ·[|W| = m], i.e. Φ(y) = λ·K_m(|y|; 2m), with K_r(h; n) = Σ_{|W|=r} χ_W(y) for |y| = h.
   - Krawtchouk reciprocity C(n,h)K_r(h) = C(n,r)K_h(r), together with K_h(m; 2m) = [z^h](1−z)^m(1+z)^m = [z^h](1−z²)^m, gives

     K_m(h; 2m) = 0 for h odd,  and  K_m(2i; 2m) = (−1)^i·C(m,i)·C(2m,m)/C(2m,2i).
3. **k odd.** φ lives on odd h, where K_m vanishes. At h = 0, K_m(0) = C(2m,m) ≠ 0 forces λ = 0, so F|_S = 0. Every word lies in some sector with m ≥ 1 (1^k ∉ W_k), so F = 0. Palette 1 together with (A) already suffices.
4. **k = 2K even.** Since (−1)^{C(2i,2)}(−1)^i = 1, and using C(m,i)/C(2m,2i) = (2i−1)!!(2m−2i−1)!!/(2m−1)!!, writing contents as n = 2μ gives

   g(2μ) = A(μ_1)·D(μ_2)·D(μ_3),  with  D(j) = (2j−1)!! > 0.

   Here A(K − m) = g(k−2m, 2m, 0)/D(m) for m ≥ 1, and A(K) = g(2K, 0, 0).
5. **Palette 2.** F ∈ B_2 iff F∘τ ∈ B_1. Since inv(τw) ≡ inv(w) + n_1n_2 and n_1 is even, F∘τ = (−1)^{inv}·(g∘τ)(n). Step 4 applied to F∘τ gives g(2μ) = A'(μ_2)·D(μ_1)·D(μ_3).
   - Comparing the two forms at μ_2 = 0 gives A(μ_1) = A'(0)·D(μ_1). Hence g(2μ) = λ·D(μ_1)D(μ_2)D(μ_3).
6. **(S).** For ρ a composition of K − 1 (K ≥ 1),

   Σ_r g(2ρ + 2e_r) = λ·D(ρ)·Σ_r (2ρ_r + 1) = λ·D(ρ)·(2K + 1) = 0,

   so λ = 0 and F = 0. ∎

*Remark [PROVED; numerically confirmed for k ≤ 7].* For k even, N_k ∩ B_1 is one-dimensional, spanned by A(j+1) = −2(K−j)·A(j). For k odd it is 0. So one palette is never enough, and the second palette is used in exactly one place, step 5.

---

## 5. The free theorem and the main theorem

**Theorem 5.1 [PROVED] (free theorem).** For every finite cyclically ordered V, 𝔅_1 ∩ 𝔅_2 = 𝔏. Consequently dim X = Cat_k (by §6, the α_σ are independent).

*Proof.* Induct on k = |V|.

- **Base, k = 1.** The only Y that is b-matchable is ∅, so 𝔅_1 is the functions of b alone and 𝔅_2 is the functions of a alone. X is the constants, which equals 𝔏.
- **Step, k ≥ 2.** Since 𝔏 ⊆ X (Corollary 3.2), it suffices to show X ∩ 𝔏^⊥ = 0. Let f ∈ X ∩ 𝔏^⊥.
  1. For each v, E_v f ∈ X ∩ 𝔏^⊥ (Lemma 3.4) and is independent of c_v. Lemma 3.5 and induction give E_v f = 0.
  2. For each adjacent pair v, w, Lemma 3.6 and induction give f_e = 0. So f vanishes on every improper colouring.
  3. f is translation invariant (Corollary 3.2), so f = F∘t.
  4. Lemma 4.1 gives F ∈ B_1 ∩ B_2, and Lemma 4.2 gives F ∈ N_k. Lemma 4.4 gives F = 0. ∎

**Proof of Theorem A [PROVED].** Let P = Π_{edges} (1 − Q_{vw}) be multiplication by [c proper].

- (⊇) Pα_σ is supported on proper colourings, translation invariant, and lies in X (Lemma 3.4 and Corollary 3.2). On proper colourings Pα_σ = ζ_σ∘t. Lemma 4.1 gives ζ_σ ∈ B_1 ∩ B_2.
- (⊆) Take F ∈ B_1 ∩ B_2 and let f = F∘t on proper colourings, 0 elsewhere. Lemma 4.1 and Theorem 5.1 give f ∈ X = 𝔏, so f = Pf ∈ P𝔏.
  - If σ has two adjacent vertices in one block, then Pα_σ = 0. Otherwise Pα_σ = ζ_σ∘t.
  - Hence F ∈ span{ζ_σ : σ ∈ 𝓡_k} = BL_k.
- **All pairs of palettes.** Every permutation of the three letters is induced by some M ∈ GL₂(F₂) ≅ S_3, acting on colours and letterwise on words. M maps α-Kempe blocks onto Mα-Kempe blocks, so B_{Mα} = B_α∘M^{−1}.
  - M fixes every ζ_σ, because the colouring of Mt is Mc(t) and constancy on blocks is preserved.
  - So B_{Mα} ∩ B_{Mβ} = BL_k for every M. Any pair of palettes is the image of {1, 2}.
  - Then BL_k ⊆ B_3, and B_1∩B_2∩B_3 = BL_k. ∎

---

## 6. dim BL_k = R_k

**Lemma 6.1 [PROVED] (triangularity).**
- Pα_σ = Σ_{E'⊆E} (−1)^{|E'|} α_{σ∨E'}, and every σ∨E' is NC (Lemma 3.3).
- Take σ ∈ 𝓡_k. If E' ≠ ∅, then σ∨E' has an adjacent pair in one block, so σ∨E' ∉ 𝓡_k.
- So the α_τ-coefficient of Pα_σ, for τ ∈ 𝓡_k, is δ_{στ}.
- Therefore, if {α_π : π ∈ NC(V)} is linearly independent, so is {Pα_σ = ζ_σ∘t : σ ∈ 𝓡_k}. Since t is onto W_k, dim BL_k = |𝓡_k|.

**Lemma 6.2 [PROVED] (independence at Q = 4).** The functions {α_π : π ∈ NC(k)} on 4-colourings are linearly independent. Equivalently, the chromatic-joins Gram matrix G_{στ} = ⟨α_σ, α_τ⟩ = 4^{#(σ∨τ)} is positive definite.

*Proof.*

1. **Meander encoding.** Put 2k points on a circle, with ring vertex i owning points 2i and 2i+1. Let m(σ) be the NC perfect matching that pairs 2i+1 with 2·next_σ(i), where next_σ(i) is the next element of i's block in cyclic order. This is the boundary of the fattened blocks; a singleton gives the pair {2i, 2i+1}. m is injective, since next_σ can be read off.
2. **Loop formula.** Draw the block-stars of σ in the northern hemisphere and those of τ in the southern hemisphere. Together they form a planar graph Γ with k + |σ| + |τ| vertices, 2k edges and #(σ∨τ) components.
   - Its regular neighbourhood F ⊂ S² has χ(F) = |σ| + |τ| − k.
   - Each component of F is a sphere with holes, so the number of boundary circles is 2#(σ∨τ) − χ(F).
   - Those boundary circles are exactly the ℓ(m(σ), m(τ)) loops of the meander system m(σ) ∪ m(τ). Hence

     G_{στ} = 2^{ℓ(m(σ),m(τ))}·2^{|σ|−k/2}·2^{|τ|−k/2},

     so G = D·L·D, where L_{ab} = 2^{ℓ(a,b)} is restricted to the image of m.
3. **Rumer vectors.** Relabel the 2k points as 1, …, 2k. For an NC perfect matching a of [2k], let v_a = ⊗_{{i<j}∈a} (e_1⊗e_2 − e_2⊗e_1)_{ij} ∈ (ℝ²)^{⊗2k}.
   - v_a(x)v_b(x) ≠ 0 iff x ∈ {1,2}^{2k} properly 2-colours every loop of a ∪ b. There are 2^{ℓ(a,b)} such x.
   - Flipping one loop changes the sign by (−1)^{#a-pairs + #b-pairs on it} = +1, since the loop alternates a-pairs and b-pairs.
   - At the alternating colouring x_i = 1 + [i even], which suits every NC matching, the value is ε_aε_b with ε_a = (−1)^{#{pairs with even left end}}.
   - So ⟨v_a, v_b⟩ = ε_aε_b·2^{ℓ(a,b)}, and L is a signed Gram matrix of the v_a.
4. **Independence of the v_a.** Let x^a put 1 at the openers and 2 at the closers of a, so v_a(x^a) = 1.
   - If v_b(x^a) ≠ 0, then each pair of b is coloured {1,2} by x^a. So for every prefix [1, p], the Dyck heights satisfy h_a(p) = Σ (±1) over b-arcs cut by the prefix ≤ h_b(p).
   - Ordering matchings by area Σ_p h(p), the matrix (v_b(x^a)) is unitriangular, because a Dyck path determines its NC matching.
   - So the v_a are independent, L is positive definite, its principal submatrix on m(NC) is positive definite, and so is G. ∎

**Lemma 6.3 [PROVED] (counting).** |𝓡_k| is the Riordan number R_k = Σ_{j} (−1)^{k−j} C(k,j)·Cat_j.

*Proof.*
- **Kreweras complement.** Interleave the points 1, 1', 2, 2', …, k, k'. Then i, i+1 (cyclically) lie in one block of σ iff i' is a singleton of the Kreweras complement K(σ).
  - (⇒) The chord {i, i+1} isolates i'.
  - (⇐) Suppose i and i+1 lie in different blocks of σ. Let l be the last element of the block B of i+1, reading cyclically from i+1. No block of σ meets both arcs cut by the chord i'–l': B lies on one side, and any other block meeting both sides would cross B. So i' ~ l' with l' ≠ i'.
  - Hence K restricts to a bijection from 𝓡_k onto the singleton-free NC partitions.
- **Counting singleton-free partitions.** Deleting the singletons of an arbitrary NC partition leaves a singleton-free NC partition of the remaining points, and the construction reverses. So Cat_k = Σ_j C(k,j)·r_j, and binomial inversion gives r_k = Σ_j (−1)^{k−j} C(k,j) Cat_j.
  - These are the Riordan numbers (OEIS A005043): 1, 0, 1, 1, 3, 6, 15, 36, 91, 232, 603, 1585, …
  - They have generating function (1+x−√(1−2x−3x²))/(2x(1+x)) and satisfy (n+1)R_n = (n−1)(2R_{n−1} + 3R_{n−2}). Both were checked against the binomial formula for n ≤ 13. ∎

---

## 7. Remarks

- **Two palettes suffice [PROVED].** The proof shows B_α ∩ B_β = BL_k for every pair. Palette 2 is used only in step 5 of Lemma 4.4 (k even).
- **Spectral gap [CONJECTURED].** Numerically, for k = 2..9, the cosine of the smallest nonzero principal angle between B_1 and B_2 (the largest singular value below 1 of Q_1Q_2ᵀ) equals 0.500 exactly, i.e. 60°. I have no proof for general k.
- **Corollary 6.3 of the memo [PROVED].** It is now unconditional for all k: every vector feasible for the B model lies in BL_k. In the memo's language, Kempe chains impose no linear relation beyond Birkhoff–Lewis, for any ring size.
- **The memo's §7 heuristic "Q = 4 is not a Beraha number".** For the purpose used here it is replaced by the rigorous Lemma 6.2.
- **Temperley–Lieb [not used].** The Rumer vectors span the SU(2)-singlet space of (ℂ²)^{⊗2k}, i.e. a TL_{2k}(δ = ±2) module. Lemma 6.2 is the statement that the meander (Gram) form is nondegenerate at loop weight 2.
- **Free dimensions [PROVED].** dim 𝔅_α = C(2k,k) and dim 𝔅_1 ∩ 𝔅_2 = Cat_k.

---

## 8. Literature and attribution (honest status)

**Verified by reading the source this session.**

- *Z. Dvořák, B. Lidický, "Coloring count cones of planar graphs".* Source: arXiv:1907.04066, v2, revised 25 Oct 2021. The arXiv page lists related DOI 10.1002/jgt.22767, a Wiley/J. Graph Theory prefix. I did not resolve the DOI, so "JGT 2022" is taken from the brief.
  - The paper works with cones of colouring-count vectors and Kempe-chain signatures (their Theorem 5: n_G ∈ B_d).
  - The parts I read contain no linear-span, dimension, Birkhoff–Lewis-span or Riordan statement.
  - Their references include D. I. A. Cohen, "Block count consistency and the four color problem" (manuscript), and S. J. Gismondi, E. R. Swart, "A new type of 4-colour reducibility", Congr. Numer. 82 (1991) 33–48.
- *D. Marcotte, "On the Birkhoff–Lewis Equations"* (Waterloo C&O essay, PDF on uwaterloo.ca). It is expository. It uses "simple partitions" and gives reduced dimensions 3, 6, 15 for rings 4, 5, 6, which agree with R_k on the BL side. It does not treat Kempe spans.
  - Its bibliography gives: W. T. Tutte, "On the Birkhoff–Lewis equations", Discrete Math. 92 (1991) 417–425; W. T. Tutte, "The Birkhoff–Lewis equations for graph-colorings", Ann. Discrete Math. 55 (1993) 153–158; G. D. Birkhoff, D. C. Lewis, "Chromatic polynomials", Trans. AMS 60 (1946) 355–451; and Cautis–Jackson (below).

**Bibliographic data verified by search; content not read in full.**

- W. T. Tutte, "The matrix of chromatic joins", J. Combin. Theory Ser. B 57 (1993) 269–288, DOI 10.1006/jctb.1993.1021.
- D. M. Jackson, "The lattice of noncrossing partitions and the Birkhoff–Lewis equations", European J. Combin. (1994), DOI 10.1006/eujc.1994.1026.
- S. Cautis, D. M. Jackson, "The matrix of chromatic joins and the Temperley–Lieb algebra", JCTB 89 (2003) 109–155, DOI 10.1016/S0095-8956(03)00071-6.
- P. Fendley, V. Krushkal, "Tutte chromatic identities from the Temperley–Lieb algebra", Geom. Topol. 13 (2009) 709–741, DOI 10.2140/gt.2009.13.709. It derives Tutte's golden identity at Q = φ+1 from TL.
- F. R. Bernhart, "Catalan, Motzkin, and Riordan numbers", Discrete Math. 204 (1999) 73–112, DOI 10.1016/S0012-365X(99)00054-0. Its content (the Riordan count via NC partitions) is known to me only secondhand.
- D. Cohen, V. Miller, "On the four color problem" (1987, Séminaire Lotharingien de Combinatoire). It has a section titled "Block count consistency". I did not read it in full.

**From memory only (not verified this session).**

- Tutte's 1993 matrix 4^{#(σ∨τ)}, or Q^{#(σ∨τ)} in general, has a determinant that factors into Chebyshev-type terms and vanishes only at Beraha numbers. This is studied by Tutte, Dahab, and Cautis–Jackson, and it is related to the meander determinant of Di Francesco–Golinelli–Guitter (Comm. Math. Phys. 186, 1997).
- Linear independence of Rumer diagrams is classical (Rumer 1932).
- Both points would give Lemma 6.2. It is proved here independently.

**Not found anywhere.**

- No source I found states that the Kempe block spans of the palettes intersect exactly in the Birkhoff–Lewis span, that two palettes suffice, or the formula dim B_α = (T_k + (−1)^k)/2. The closest material is Cohen's block-count consistency, in an unpublished manuscript I could not access, and the Dvořák–Lidický cones, which are not spans.
- The facts dim BL_k = R_k, the chromatic-joins matrix, and the Birkhoff–Lewis equations themselves are classical. The Riordan/NC-partition count and the Q = 4 nonsingularity should be credited to the literature above, even though they are reproved here.
- **Fair attribution:** Theorem A appears to be new as a statement, but it is a sharpening of well-known themes. Experts in block-count consistency (Cohen; Gismondi–Swart) may have known equivalent facts in unpublished form. I cannot rule that out.

---

## 9. Numerical evidence (`python3 theorem62_check.py`, about 3.5 s, single thread)

The script checks the following:
- the closed form for k ≤ 12;
- Lemma 2.2 against the literal Kempe block indicators for k ≤ 6;
- the NC and Riordan counts and the rank of {ζ_σ};
- BL ⊆ B_α for every palette (residual);
- dim(B_1∩B_2) = R_k for k ≤ 9 and dim(B_1∩B_3) = R_k for k ≤ 8;
- dim N_k and the explicit (−1)^{inv}g family, plus dim(N∩B_1) = [k even] and N∩B_1∩B_2 = 0, for k ≤ 7;
- dim 𝔅_α = C(2k,k) and dim(𝔅_1∩𝔅_2) = Cat_k, for k ≤ 5;
- injectivity of m, the loop formula, and positive definiteness of G, for k ≤ 6.

```
dim B_alpha = (T_k+(-1)^k)/2 : {2: 2, 3: 3, 4: 10, 5: 25, 6: 71, 7: 196, 8: 554, 9: 1569, 10: 4477, 11: 12826}
 k  words  dimB  dim(B1∩B2) dim(B1∩B3)  R_k  BL-resid   next-sv  dimN  dim(N∩B1)  N∩B1∩B2
 2      3     2         1          1      1  2.2e-16  0.500     2         1       0
 3      6     3         1          1      1  2.2e-16  0.500     1         0       0
 4     21    10         3          3      3  2.2e-16  0.500     3         1       0
 5     60    25         6          6      6  2.2e-16  0.500     2         0       0
 6    183    71        15         15     15  4.4e-16  0.500     4         1       0
 7    546   196        36         36     36  4.4e-16  0.500     3         0       0
 8   1641   554        91         91     91  1.3e-15  0.500     -         -       -
 9   4920  1569       232          -    232  1.3e-15  0.500     -         -       -
free k=1: dim Bfrak_1 = 2 = C(2k,k), dim(Bfrak_1 ∩ Bfrak_2) = 1 = Catalan = dim Lfrak
   ... (k = 2..5: 6, 20, 70, 252 = C(2k,k) and 2, 5, 14, 42 = Catalan)
joins k=1: loops = 2#(s v t)+k-|s|-|t| ok; Gram 4^#(s v t) PD (cond^-1 1.00e+00)
   ... (k = 2..6 likewise; cond^-1 down to 7.62e-07 at k = 6)
ALL CHECKS PASSED  (3.0s)
```

(Two output blocks are abbreviated with "..."; the full output has one line per k.)

The row for k = 4..9 reproduces the memo's §6 table (21/60/…/4920 words; dimensions 10/…/1569; intersection 3/…/232).

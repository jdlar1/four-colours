import Theorem62.Count

/-!
# Theorem A, inclusion `BL_k ⊆ 𝔅_α` (hence `BL_k ⊆ 𝔅_α ⊓ 𝔅_β`)

For a noncrossing partition `σ`, the condition "the ring colouring is constant on every block"
is equivalent to `c a = c b` for the pairs `(a, b)` with `a < b`, `a ~ b` and `a` the least
element of its block (`minPairs σ`). The intervals `[a, b)` of these pairs form a laminar
family (this is where noncrossing is used). On each sector `S`,
`[c a = c b] = [#([a,b) ∩ S) even] · (1 + chi [a,b)) / 2`, and expanding the product gives
characters of symmetric differences of laminar even intervals, which are balanced.
-/

namespace Theorem62

open Finset

variable {k : ℕ}

/-! ### Intervals and odd-multiplicity sets -/

/-- The interval `[a, b)` of `Fin k`. -/
def ico (a b : Fin k) : Finset (Fin k) := univ.filter (fun l => a ≤ l ∧ l < b)

theorem mem_ico {a b l : Fin k} : l ∈ ico a b ↔ a ≤ l ∧ l < b := by
  simp [ico]

/-- The points covered an odd number of times by the family `I p`, `p ∈ Q`
(the iterated symmetric difference). -/
def oddSet {ι : Type*} (I : ι → Finset (Fin k)) (Q : Finset ι) : Finset (Fin k) :=
  univ.filter (fun l => #(Q.filter (fun p => l ∈ I p)) % 2 = 1)

theorem oddSet_empty {ι : Type*} (I : ι → Finset (Fin k)) : oddSet I ∅ = ∅ := by
  ext l; simp [oddSet]

theorem oddSet_insert {ι : Type*} [DecidableEq ι] (I : ι → Finset (Fin k)) {a : ι}
    {Q : Finset ι} (ha : a ∉ Q) : oddSet I (insert a Q) = symmDiff (I a) (oddSet I Q) := by
  ext l
  simp only [oddSet, mem_filter, mem_univ, true_and, mem_symmDiff, filter_insert]
  by_cases hl : l ∈ I a
  · rw [if_pos hl, card_insert_of_notMem (fun h => ha (mem_filter.mp h).1)]
    constructor
    · intro h; left; exact ⟨hl, by omega⟩
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · omega
      · exact absurd hl h
  · rw [if_neg hl]
    constructor
    · intro h; right; exact ⟨h, hl⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact absurd h hl
      · exact h

/-- In a family where `X` is nested in or disjoint from every member, `X` is nested in or
disjoint from the symmetric difference. -/
theorem laminar_oddSet {ι : Type*} [DecidableEq ι] (I : ι → Finset (Fin k)) (X : Finset (Fin k))
    (Q : Finset ι) (h : ∀ q ∈ Q, X ⊆ I q ∨ Disjoint X (I q)) :
    X ⊆ oddSet I Q ∨ Disjoint X (oddSet I Q) := by
  induction Q using Finset.induction_on with
  | empty => right; rw [oddSet_empty]; exact disjoint_empty_right _
  | insert a Q ha ih =>
    rw [oddSet_insert I ha]
    have h1 := h a (mem_insert_self a Q)
    have h2 := ih (fun q hq => h q (mem_insert_of_mem hq))
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · right
      rw [disjoint_left]
      intro x hx hx'
      rw [mem_symmDiff] at hx'
      rcases hx' with ⟨_, hn⟩ | ⟨_, hn⟩
      · exact hn (h2 hx)
      · exact hn (h1 hx)
    · left
      intro x hx
      rw [mem_symmDiff]
      exact Or.inl ⟨h1 hx, disjoint_left.mp h2 hx⟩
    · left
      intro x hx
      rw [mem_symmDiff]
      exact Or.inr ⟨h2 hx, disjoint_left.mp h1 hx⟩
    · right
      rw [disjoint_left]
      intro x hx hx'
      rw [mem_symmDiff] at hx'
      rcases hx' with ⟨hm, _⟩ | ⟨hm, _⟩
      · exact disjoint_left.mp h1 hx hm
      · exact disjoint_left.mp h2 hx hm

/-- An additive weight vanishing on every member of a laminar family vanishes on every
symmetric difference of members. -/
theorem sum_oddSet_eq_zero {ι : Type*} [DecidableEq ι] (I : ι → Finset (Fin k)) (g : Fin k → ℤ)
    (P : Finset ι) (h0 : ∀ p ∈ P, ∑ u ∈ I p, g u = 0)
    (hlam : ∀ p ∈ P, ∀ q ∈ P, I p ⊆ I q ∨ I q ⊆ I p ∨ Disjoint (I p) (I q))
    (hinj : ∀ p ∈ P, ∀ q ∈ P, I p = I q → p = q) :
    ∀ Q ⊆ P, ∑ u ∈ oddSet I Q, g u = 0 := by
  suffices H : ∀ n, ∀ Q ⊆ P, #Q = n → ∑ u ∈ oddSet I Q, g u = 0 from
    fun Q hQ => H _ Q hQ rfl
  intro n
  induction n with
  | zero =>
    intro Q _ hQ
    rw [card_eq_zero.mp hQ, oddSet_empty, sum_empty]
  | succ n ih =>
    intro Q hQP hQ
    have hne : Q.Nonempty := card_pos.mp (by omega)
    obtain ⟨p, hpQ, hmin⟩ := Q.exists_min_image (fun p => #(I p)) hne
    have hQ' : Q.erase p ⊆ P := (erase_subset p Q).trans hQP
    have hcard : #(Q.erase p) = n := by rw [card_erase_of_mem hpQ]; omega
    have hrec := ih (Q.erase p) hQ' hcard
    have hsplit : oddSet I Q = symmDiff (I p) (oddSet I (Q.erase p)) := by
      conv_lhs => rw [← insert_erase hpQ]
      exact oddSet_insert I (notMem_erase p Q)
    have hlam' : ∀ q ∈ Q.erase p, I p ⊆ I q ∨ Disjoint (I p) (I q) := by
      intro q hq
      have hqQ := mem_of_mem_erase hq
      have hqp := ne_of_mem_erase hq
      rcases hlam p (hQP hpQ) q (hQP hqQ) with h | h | h
      · exact Or.inl h
      · exfalso
        have := eq_of_subset_of_card_le h (hmin q hqQ)
        exact hqp (hinj q (hQP hqQ) p (hQP hpQ) this)
      · exact Or.inr h
    rw [hsplit]
    rcases laminar_oddSet I (I p) (Q.erase p) hlam' with h | h
    · rw [symmDiff_of_le h]
      have := sum_sdiff (f := g) h
      rw [h0 p (hQP hpQ), hrec] at this
      linarith
    · rw [h.symmDiff_eq_sup, sup_eq_union, sum_union h, h0 p (hQP hpQ), hrec, add_zero]

/-! ### Balanced weights of intervals -/

theorem rank_eq_add {S : Finset (Fin k)} {a b u : Fin k} (hu : u ∈ (ico a b).filter (· ∈ S)) :
    rank S u = rank S a + rank ((ico a b).filter (· ∈ S)) u := by
  rw [mem_filter, mem_ico] at hu
  unfold rank
  rw [← card_filter_add_card_filter_not (s := S.filter (· < u)) (fun l => l < a)]
  have e1 : (S.filter (· < u)).filter (· < a) = S.filter (· < a) := by
    ext l
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, lt_of_lt_of_le h3 hu.1.1⟩, h3⟩
  have e2 : (S.filter (· < u)).filter (fun l => ¬ l < a) =
      ((ico a b).filter (· ∈ S)).filter (· < u) := by
    ext l
    simp only [mem_filter, mem_ico, not_lt]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h3, lt_trans h2 hu.1.2⟩, h1⟩, h2⟩
    · rintro ⟨⟨⟨h3, _⟩, h1⟩, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
  rw [e1, e2]

/-- An interval meeting `S` in an even number of points is balanced in `S`. -/
theorem sum_ico_eq_zero {S : Finset (Fin k)} {a b : Fin k}
    (h : Even #((ico a b).filter (· ∈ S))) :
    ∑ u ∈ (ico a b).filter (· ∈ S), (-1 : ℤ) ^ rank S u = 0 := by
  have hb := balanced_self h
  unfold Balanced at hb
  rw [sum_congr rfl (fun u hu => by rw [rank_eq_add hu, pow_add]), ← mul_sum, hb, mul_zero]

/-- The signed weight of `S`. -/
def wS (S : Finset (Fin k)) (u : Fin k) : ℤ := if u ∈ S then (-1) ^ rank S u else 0

theorem sum_wS (S U : Finset (Fin k)) :
    ∑ u ∈ U, wS S u = ∑ u ∈ U.filter (· ∈ S), (-1 : ℤ) ^ rank S u := by
  rw [sum_filter]; rfl

/-! ### The minimal pairs of a noncrossing partition -/

open Classical in
/-- Pairs `(a, b)`, `a < b`, in a common block, with `a` the least element of its block. -/
noncomputable def minPairs (σ : NoncrossingPartition k) : Finset (Fin k × Fin k) :=
  univ.filter (fun p => p.1 < p.2 ∧ σ.rel p.1 p.2 ∧ ∀ l, l < p.1 → ¬ σ.rel l p.1)

theorem mem_minPairs {σ : NoncrossingPartition k} {p : Fin k × Fin k} :
    p ∈ minPairs σ ↔ p.1 < p.2 ∧ σ.rel p.1 p.2 ∧ ∀ l, l < p.1 → ¬ σ.rel l p.1 := by
  unfold minPairs
  simp only [mem_filter, mem_univ, true_and]

theorem forall_rel_of_minPairs (σ : NoncrossingPartition k) (c : Fin k → F22)
    (h : ∀ p ∈ minPairs σ, c p.1 = c p.2) : ∀ i j, σ.rel i j → c i = c j := by
  classical
  have key : ∀ i, ∃ m, σ.rel m i ∧ ∀ l, σ.rel l i → m ≤ l := by
    intro i
    have hi : i ∈ univ.filter (fun l => σ.rel l i) :=
      mem_filter.mpr ⟨mem_univ _, σ.equiv.refl i⟩
    have hA : (univ.filter (fun l => σ.rel l i)).Nonempty := ⟨i, hi⟩
    refine ⟨(univ.filter (fun l => σ.rel l i)).min' hA,
      (mem_filter.mp ((univ.filter (fun l => σ.rel l i)).min'_mem hA)).2, ?_⟩
    intro l hl
    exact (univ.filter (fun l => σ.rel l i)).min'_le l (mem_filter.mpr ⟨mem_univ _, hl⟩)
  have toMin : ∀ m x, σ.rel m x → m ≤ x → (∀ l, l < m → ¬ σ.rel l m) → c m = c x := by
    intro m x hr hle hmin
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq]
    · exact h (m, x) (mem_minPairs.mpr ⟨hlt, hr, hmin⟩)
  intro i j hij
  obtain ⟨m, hmi, hm⟩ := key i
  have hmin : ∀ l, l < m → ¬ σ.rel l m := by
    intro l hl hlm
    exact absurd (hm l (σ.equiv.trans hlm hmi)) (not_le.mpr hl)
  have h1 := toMin m i hmi (hm i (σ.equiv.refl i)) hmin
  have h2 := toMin m j (σ.equiv.trans hmi hij) (hm j (σ.equiv.symm hij)) hmin
  rw [← h1, h2]

theorem minPairs_laminar (σ : NoncrossingPartition k) {p q : Fin k × Fin k}
    (hp : p ∈ minPairs σ) (hq : q ∈ minPairs σ) :
    ico p.1 p.2 ⊆ ico q.1 q.2 ∨ ico q.1 q.2 ⊆ ico p.1 p.2 ∨ Disjoint (ico p.1 p.2) (ico q.1 q.2) := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  rw [mem_minPairs] at hp hq
  obtain ⟨_, rab, mina⟩ := hp
  obtain ⟨_, rcd, minc⟩ := hq
  simp only at *
  by_cases h1 : b ≤ c
  · right; right
    rw [disjoint_left]
    intro l hl hl'
    rw [mem_ico] at hl hl'
    exact absurd (lt_of_lt_of_le hl.2 h1) (not_lt.mpr hl'.1)
  by_cases h2 : d ≤ a
  · right; right
    rw [disjoint_left]
    intro l hl hl'
    rw [mem_ico] at hl hl'
    exact absurd (lt_of_lt_of_le hl'.2 h2) (not_lt.mpr hl.1)
  push_neg at h1 h2
  by_cases h3 : a ≤ c
  · by_cases h4 : d ≤ b
    · right; left
      intro l hl
      rw [mem_ico] at hl ⊢
      exact ⟨le_trans h3 hl.1, lt_of_lt_of_le hl.2 h4⟩
    · push_neg at h4
      rcases eq_or_lt_of_le h3 with h5 | h5
      · left
        intro l hl
        rw [mem_ico] at hl ⊢
        exact ⟨h5 ▸ hl.1, lt_trans hl.2 h4⟩
      · exfalso
        exact minc a h5 (σ.noncrossing a b c d h5 h1 h4 rab rcd)
  · push_neg at h3
    by_cases h4 : b ≤ d
    · left
      intro l hl
      rw [mem_ico] at hl ⊢
      exact ⟨le_trans (le_of_lt h3) hl.1, lt_of_lt_of_le hl.2 h4⟩
    · push_neg at h4
      exfalso
      exact mina c h3 (σ.noncrossing c d a b h3 h2 h4 rcd rab)

theorem ico_inj {a b c d : Fin k} (hab : a < b) (hcd : c < d) (h : ico a b = ico c d) :
    (a, b) = (c, d) := by
  have ha : a ∈ ico c d := h ▸ (mem_ico.mpr ⟨le_refl a, hab⟩)
  have hc : c ∈ ico a b := h.symm ▸ (mem_ico.mpr ⟨le_refl c, hcd⟩)
  rw [mem_ico] at ha hc
  have hac : a = c := le_antisymm hc.1 ha.1
  have hbd : b = d := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : b ∈ ico c d := mem_ico.mpr ⟨by rw [← hac]; exact hab.le, hlt⟩
      rw [← h, mem_ico] at this
      exact lt_irrefl _ this.2
    · have : d ∈ ico a b := mem_ico.mpr ⟨by rw [hac]; exact hcd.le, hlt⟩
      rw [h, mem_ico] at this
      exact lt_irrefl _ this.2
  rw [hac, hbd]

/-! ### Characters and the edge indicator -/

section Chars

variable {α : TaitColor}

theorem ringColor_add_ico (t : TaitWord k) {a b : Fin k} (hab : a ≤ b) :
    ringColor t b = ringColor t a + ∑ l ∈ ico a b, (t.1 l).1 := by
  unfold ringColor
  have hset : univ.filter (fun j : Fin k => j < b) = univ.filter (fun j => j < a) ∪ ico a b := by
    ext l
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_ico]
    constructor
    · intro hl
      by_cases h : l < a
      · exact Or.inl h
      · exact Or.inr ⟨not_lt.mp h, hl⟩
    · rintro (h | h)
      · exact lt_of_lt_of_le h hab
      · exact h.2
  rw [hset, sum_union]
  rw [disjoint_left]
  intro l h1 h2
  rw [mem_filter] at h1
  rw [mem_ico] at h2
  exact absurd h1.2 (not_lt.mpr h2.1)

theorem psi_alpha_sum (t : TaitWord k) (I : Finset (Fin k)) :
    psi α.1 (∑ l ∈ I, (t.1 l).1) = (-1) ^ #(I.filter (· ∈ sector α t)) := by
  rw [← prod_psi α.2, ← prod_const, prod_filter]
  apply prod_congr rfl
  intro l _
  by_cases h : l ∈ sector α t
  · rw [if_pos h]; exact psi_of_ne (t.1 l).2 (val_ne_of_mem_sector h)
  · rw [if_neg h]
    rw [mem_sector, not_not] at h
    simp [psi, h]

theorem psi_other_sum (t : TaitWord k) (I : Finset (Fin k)) :
    psi (other α).1 (∑ l ∈ I, (t.1 l).1) = chi α I t := by
  rw [← prod_psi (other α).2]; rfl

theorem ind_zero_eq {a b : F22} (hab : a ≠ b) (x : F22) :
    (if x = 0 then (1 : K) else 0) = (1 + psi a x) / 2 * ((1 + psi b x) / 2) := by
  unfold psi
  by_cases h0 : x = 0
  · simp only [h0, true_or, if_true]; norm_num
  · rw [if_neg h0]
    by_cases h1 : x = a
    · have h2 : x ≠ b := h1 ▸ hab
      rw [if_pos (Or.inr h1), if_neg (by tauto)]; norm_num
    · rw [if_neg (by tauto)]; norm_num

/-- `[c a = c b] = [#([a,b) ∩ S) even] · (1 + chi [a,b)) / 2` on a word with sector `S`. -/
theorem ind_ringColor_eq (t : TaitWord k) {a b : Fin k} (hab : a ≤ b) :
    (if ringColor t a = ringColor t b then (1 : K) else 0) =
      (1 + (-1) ^ #((ico a b).filter (· ∈ sector α t))) / 2 * ((1 + chi α (ico a b) t) / 2) := by
  rw [← psi_alpha_sum, ← psi_other_sum, ← ind_zero_eq (other_ne α).symm, ringColor_add_ico t hab]
  by_cases hx : ∑ l ∈ ico a b, (t.1 l).1 = 0
  · rw [if_pos hx, if_pos (by rw [hx, add_zero])]
  · rw [if_neg hx, if_neg]
    intro h
    exact hx (add_left_cancel (h.symm.trans (add_zero _).symm))

theorem chi_oddSet {ι : Type*} [DecidableEq ι] (I : ι → Finset (Fin k)) (Q : Finset ι)
    (t : TaitWord k) : chi α (oddSet I Q) t = ∏ p ∈ Q, chi α (I p) t := by
  induction Q using Finset.induction_on with
  | empty => rw [oddSet_empty, prod_empty]; simp [chi]
  | insert a Q ha ih => rw [oddSet_insert I ha, ← chi_mul, prod_insert ha, ih]

/-- Off the sector every sign is `-1`. -/
theorem chi_split (t : TaitWord k) (U : Finset (Fin k)) :
    chi α U t = (-1) ^ #(U.filter (· ∉ sector α t)) * chi α (U.filter (· ∈ sector α t)) t := by
  unfold chi
  rw [← prod_filter_mul_prod_filter_not U (· ∈ sector α t), mul_comm, ← prod_const]
  congr 1
  apply prod_congr rfl
  intro l hl
  rw [mem_filter, mem_sector, not_not] at hl
  unfold sgn
  rw [hl.2]
  exact psi_of_ne α.2 (other_ne α).symm

/-- A sector-restricted character whose trace on the sector is balanced lies in `𝔅_α`. -/
theorem fiberChi_mem (S U : Finset (Fin k)) (hbal : Balanced S (U.filter (· ∈ S))) :
    (fun t : TaitWord k => if sector α t = S then chi α U t else 0) ∈ kempeSpan k α := by
  by_cases hS : ∃ t : TaitWord k, sector α t = S
  · have heq : (fun t : TaitWord k => if sector α t = S then chi α U t else 0) =
        ((-1 : K) ^ #(U.filter (· ∉ S))) • fS α S (U.filter (· ∈ S)) := by
      funext t
      simp only [Pi.smul_apply, smul_eq_mul, fS]
      by_cases h : sector α t = S
      · rw [if_pos h, if_pos h, chi_split t U, h]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [heq, kempeSpan_eq_fourier]
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨S, _, hS, fun x hx => (mem_filter.mp hx).2, hbal, rfl⟩)
  · have heq : (fun t : TaitWord k => if sector α t = S then chi α U t else 0) = 0 := by
      funext t
      rw [if_neg (fun h => hS ⟨t, h⟩)]
      rfl
    rw [heq]
    exact Submodule.zero_mem _

end Chars

/-! ### The inclusion -/

section Incl

variable {α : TaitColor}

theorem blIndicator_eq_prod (σ : BLPartition k) (t : TaitWord k) :
    blIndicator k σ t =
      ∏ p ∈ minPairs σ.1, (if ringColor t p.1 = ringColor t p.2 then (1 : K) else 0) := by
  unfold blIndicator
  by_cases h : ∀ i j, σ.1.rel i j → ringColor t i = ringColor t j
  · rw [if_pos h]
    symm
    apply prod_eq_one
    intro p hp
    rw [if_pos (h _ _ (mem_minPairs.mp hp).2.1)]
  · rw [if_neg h]
    symm
    have h' : ¬ ∀ p ∈ minPairs σ.1, ringColor t p.1 = ringColor t p.2 :=
      fun h' => h (forall_rel_of_minPairs σ.1 _ h')
    push_neg at h'
    obtain ⟨p, hp, hne⟩ := h'
    exact prod_eq_zero hp (if_neg hne)

theorem piece_mem (σ : BLPartition k) (S : Finset (Fin k)) :
    (fun t : TaitWord k => if sector α t = S then blIndicator k σ t else 0) ∈ kempeSpan k α := by
  classical
  set P := minPairs σ.1 with hP
  set I : Fin k × Fin k → Finset (Fin k) := fun p => ico p.1 p.2 with hI
  by_cases hE : ∀ p ∈ P, Even #((I p).filter (· ∈ S))
  · have heq : (fun t : TaitWord k => if sector α t = S then blIndicator k σ t else 0) =
        ∑ Q ∈ P.powerset, ((1 / 2 : K) ^ #Q * (1 / 2 : K) ^ #(P \ Q)) •
          (fun t : TaitWord k => if sector α t = S then chi α (oddSet I Q) t else 0) := by
      funext t
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      by_cases ht : sector α t = S
      · rw [if_pos ht]
        simp only [if_pos ht]
        rw [blIndicator_eq_prod]
        have hfac : ∀ p ∈ P, (if ringColor t p.1 = ringColor t p.2 then (1 : K) else 0) =
            chi α (I p) t * (1 / 2) + 1 / 2 := by
          intro p hp
          rw [ind_ringColor_eq t (le_of_lt (mem_minPairs.mp hp).1), ht]
          have he := hE p hp
          simp only [hI] at he
          rw [he.neg_one_pow]
          ring
        rw [prod_congr rfl hfac, prod_add]
        apply sum_congr rfl
        intro Q _
        rw [prod_mul_distrib, prod_const, prod_const, chi_oddSet]
        ring
      · rw [if_neg ht]
        simp only [if_neg ht, mul_zero, sum_const_zero]
    rw [heq]
    apply Submodule.sum_mem
    intro Q hQ
    apply Submodule.smul_mem
    apply fiberChi_mem
    unfold Balanced
    rw [← sum_wS]
    refine sum_oddSet_eq_zero I (wS S) P ?_ ?_ ?_ Q (mem_powerset.mp hQ)
    · intro p hp
      rw [sum_wS]
      exact sum_ico_eq_zero (hE p hp)
    · intro p hp q hq
      exact minPairs_laminar σ.1 hp hq
    · intro p hp q hq h
      exact ico_inj (mem_minPairs.mp hp).1 (mem_minPairs.mp hq).1 h
  · push_neg at hE
    obtain ⟨p, hp, hodd⟩ := hE
    have heq : (fun t : TaitWord k => if sector α t = S then blIndicator k σ t else 0) = 0 := by
      funext t
      by_cases ht : sector α t = S
      · rw [if_pos ht, blIndicator_eq_prod]
        apply prod_eq_zero hp
        rw [ind_ringColor_eq t (le_of_lt (mem_minPairs.mp hp).1), ht,
          hodd.neg_one_pow]
        simp
      · rw [if_neg ht]; rfl
    rw [heq]
    exact Submodule.zero_mem _

/-- Every BL indicator lies in the Kempe span `𝔅_α`. -/
theorem blIndicator_mem_kempeSpan (σ : BLPartition k) : blIndicator k σ ∈ kempeSpan k α := by
  have heq : blIndicator k σ =
      ∑ S : Finset (Fin k), (fun t => if sector α t = S then blIndicator k σ t else 0) := by
    funext t
    rw [Finset.sum_apply]
    simp only [sum_ite_eq, mem_univ, if_true]
  rw [heq]
  exact Submodule.sum_mem _ (fun S _ => piece_mem σ S)

end Incl

/-- **Theorem A, inclusion `⊇`:** `BL_k ⊆ 𝔅_α`. -/
theorem blSpan_le_kempeSpan (k : ℕ) (α : TaitColor) : blSpan k ≤ kempeSpan k α := by
  rw [blSpan, Submodule.span_le]
  rintro _ ⟨σ, rfl⟩
  exact blIndicator_mem_kempeSpan σ

/-- **Theorem A, inclusion `⊇`:** `BL_k ⊆ 𝔅_α ⊓ 𝔅_β`. -/
theorem blSpan_le_inf (k : ℕ) (α β : TaitColor) :
    blSpan k ≤ kempeSpan k α ⊓ kempeSpan k β :=
  le_inf (blSpan_le_kempeSpan k α) (blSpan_le_kempeSpan k β)

end Theorem62

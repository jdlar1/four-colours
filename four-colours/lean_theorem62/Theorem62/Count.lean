import Theorem62.Fourier

/-!
# Counting the Fourier basis: Theorem B

`2 · dim (kempeSpan k α) = T_k + (-1)^k`.
-/

namespace Theorem62

open Finset

variable {k : ℕ}

instance (S U : Finset (Fin k)) : Decidable (Balanced S U) := by
  unfold Balanced; infer_instance

theorem F22_nsmul (n : ℕ) (x : F22) : n • x = if Even n then 0 else x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ih]
    by_cases h : Even n
    · rw [if_pos h, if_neg (Nat.not_even_iff_odd.mpr h.add_one), zero_add]
    · rw [if_neg h, if_pos (Nat.not_even_iff_odd.mp h).add_one, F22_add_self]

/-! ### Realizable active sets -/

theorem third_ne (α : TaitColor) : α.1 + (other α).1 ≠ (0, 0) := by
  revert α; decide

/-- The third Tait colour. -/
def third (α : TaitColor) : TaitColor := ⟨α.1 + (other α).1, third_ne α⟩

theorem other_ne' (α : TaitColor) : other α ≠ α := fun h => other_ne α (congrArg Subtype.val h)

theorem third_ne' (α : TaitColor) : third α ≠ α := by
  revert α; decide

theorem third_sum (α : TaitColor) : (third α).1 + (other α).1 + α.1 = 0 := by
  revert α; decide

theorem exists_word_even (α : TaitColor) (S : Finset (Fin k)) (hS : Even #S) (hk : Even k) :
    ∃ t : TaitWord k, sector α t = S := by
  let f : Fin k → TaitColor := fun l => if l ∈ S then other α else α
  have hsum : ∑ l, (f l).1 = 0 := by
    rw [← sum_add_sum_compl S]
    have h1 : ∑ l ∈ S, (f l).1 = #S • (other α).1 := by
      rw [← sum_const]; apply sum_congr rfl; intro l hl; simp [f, hl]
    have h2 : ∑ l ∈ Sᶜ, (f l).1 = #Sᶜ • α.1 := by
      rw [← sum_const]; apply sum_congr rfl; intro l hl; simp [f, mem_compl.mp hl]
    have hc : Even #Sᶜ := by
      rw [card_compl, Fintype.card_fin]
      obtain ⟨a, ha⟩ := hk; obtain ⟨b, hb⟩ := hS
      have : #S ≤ k := by simpa using card_le_univ S
      exact ⟨a - b, by omega⟩
    rw [h1, h2, F22_nsmul, F22_nsmul, if_pos hS, if_pos hc, add_zero]
  refine ⟨⟨f, hsum⟩, ?_⟩
  ext l
  rw [mem_sector]
  by_cases hl : l ∈ S
  · simp [f, hl, other_ne' α]
  · simp [f, hl]

theorem exists_word_odd (α : TaitColor) (S : Finset (Fin k)) (hS : Even #S) (hne : S.Nonempty)
    (hk : ¬ Even k) : ∃ t : TaitWord k, sector α t = S := by
  let m := S.min' hne
  have hm : m ∈ S := S.min'_mem hne
  let f : Fin k → TaitColor := fun l => if l = m then third α else if l ∈ S then other α else α
  have hsum : ∑ l, (f l).1 = 0 := by
    rw [← sum_add_sum_compl S, ← add_sum_erase S _ hm]
    have h0 : (f m).1 = (third α).1 := by simp [f]
    have h1 : ∑ l ∈ S.erase m, (f l).1 = #(S.erase m) • (other α).1 := by
      rw [← sum_const]; apply sum_congr rfl; intro l hl
      rw [mem_erase] at hl; simp [f, hl.1, hl.2]
    have h2 : ∑ l ∈ Sᶜ, (f l).1 = #Sᶜ • α.1 := by
      rw [← sum_const]; apply sum_congr rfl; intro l hl
      have hl' := mem_compl.mp hl
      have : l ≠ m := fun e => hl' (e ▸ hm)
      simp [f, hl', this]
    have hpos : 0 < #S := card_pos.mpr hne
    have hc1 : ¬ Even #(S.erase m) := by
      rw [card_erase_of_mem hm]
      obtain ⟨b, hb⟩ := hS
      rintro ⟨c, hc⟩; omega
    have hc2 : ¬ Even #Sᶜ := by
      rw [card_compl, Fintype.card_fin]
      have : #S ≤ k := by simpa using card_le_univ S
      obtain ⟨b, hb⟩ := hS
      rintro ⟨c, hc⟩
      exact hk ⟨b + c, by omega⟩
    rw [h0, h1, h2, F22_nsmul, F22_nsmul, if_neg hc1, if_neg hc2]
    exact third_sum α
  refine ⟨⟨f, hsum⟩, ?_⟩
  ext l
  rw [mem_sector]
  by_cases hl : l = m
  · subst hl; simp [f, third_ne' α, hm]
  · by_cases hlS : l ∈ S
    · simp [f, hl, hlS, other_ne' α]
    · simp [f, hl, hlS]

/-- **Realizability.** An active set occurs iff it has even size, and it is nonempty or `k`
is even. -/
theorem realizable_iff (α : TaitColor) (S : Finset (Fin k)) :
    (∃ t : TaitWord k, sector α t = S) ↔ Even #S ∧ (S.Nonempty ∨ Even k) := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨even_card_sector t, ?_⟩
    rcases (sector α t).eq_empty_or_nonempty with h | h
    · right
      have hall : ∀ i, t.1 i = α := by
        intro i
        by_contra hne
        have : i ∈ sector α t := mem_sector.mpr hne
        rw [h] at this
        exact absurd this (Finset.notMem_empty i)
      have hs := t.2
      simp only [hall, sum_const, card_univ, Fintype.card_fin] at hs
      rw [F22_nsmul] at hs
      by_contra hk
      rw [if_neg hk] at hs
      exact α.2 hs
    · left; exact h
  · rintro ⟨hev, h⟩
    by_cases hk : Even k
    · exact exists_word_even α S hev hk
    · exact exists_word_odd α S hev (h.resolve_right hk) hk

/-! ### Counting balanced sets -/

theorem sum_neg_one_pow_rank (S U : Finset (Fin k)) :
    ∑ u ∈ U, (-1 : ℤ) ^ rank S u =
      (#(U.filter (fun u => Even (rank S u))) : ℤ) - #(U.filter (fun u => ¬ Even (rank S u))) := by
  rw [← sum_filter_add_sum_filter_not U (fun u => Even (rank S u))]
  have h1 : ∑ u ∈ U.filter (fun u => Even (rank S u)), (-1 : ℤ) ^ rank S u =
      #(U.filter (fun u => Even (rank S u))) := by
    rw [sum_congr rfl (fun u hu => (mem_filter.mp hu).2.neg_one_pow)]; simp
  have h2 : ∑ u ∈ U.filter (fun u => ¬ Even (rank S u)), (-1 : ℤ) ^ rank S u =
      -(#(U.filter (fun u => ¬ Even (rank S u))) : ℤ) := by
    rw [sum_congr rfl (fun u hu => (Nat.not_even_iff_odd.mp (mem_filter.mp hu).2).neg_one_pow)]
    simp
  rw [h1, h2]; ring

/-- The odd-ranked elements of `S`. -/
def oddPts (S : Finset (Fin k)) : Finset (Fin k) := S.filter (fun u => ¬ Even (rank S u))

theorem card_oddPts {S : Finset (Fin k)} (hS : Even #S) : #(oddPts S) = #S / 2 := by
  have h1 := card_filter_add_card_filter_not (s := S) (fun u => Even (rank S u))
  have h2 := balanced_self hS
  unfold Balanced at h2
  rw [sum_neg_one_pow_rank] at h2
  unfold oddPts
  obtain ⟨b, hb⟩ := hS
  omega

theorem card_symmDiff_oddPts {S U : Finset (Fin k)} (hU : U ⊆ S) :
    #(symmDiff U (oddPts S)) + #(U.filter (fun u => ¬ Even (rank S u))) =
      #(U.filter (fun u => Even (rank S u))) + #(oddPts S) := by
  have hd : symmDiff U (oddPts S) = (U \ oddPts S) ∪ (oddPts S \ U) := rfl
  have hdisj : Disjoint (U \ oddPts S) (oddPts S \ U) := disjoint_sdiff_sdiff
  have hA : U \ oddPts S = U.filter (fun u => Even (rank S u)) := by
    ext u; simp only [mem_sdiff, oddPts, mem_filter, not_and, not_not]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 (hU h1)⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2⟩
  have hB : oddPts S ∩ U = U.filter (fun u => ¬ Even (rank S u)) := by
    ext u; simp only [mem_inter, oddPts, mem_filter]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨hU h1, h2⟩, h1⟩
  have hC : #(oddPts S \ U) + #(oddPts S ∩ U) = #(oddPts S) := by
    rw [← card_union_of_disjoint (disjoint_sdiff_inter _ _), sdiff_union_inter]
  rw [hd, card_union_of_disjoint hdisj, hA, ← hB]
  omega

theorem balanced_iff_card {S U : Finset (Fin k)} (hU : U ⊆ S) :
    Balanced S U ↔ #(symmDiff U (oddPts S)) = #(oddPts S) := by
  unfold Balanced
  rw [sum_neg_one_pow_rank]
  have := card_symmDiff_oddPts hU
  constructor
  · intro h; omega
  · intro h; omega

theorem symmDiff_oddPts_subset {S U : Finset (Fin k)} (hU : U ⊆ S) :
    symmDiff U (oddPts S) ⊆ S := by
  intro x hx
  rw [mem_symmDiff] at hx
  rcases hx with ⟨h, _⟩ | ⟨h, _⟩
  · exact hU h
  · exact (mem_filter.mp h).1

/-- There are `C(#S, #S/2)` balanced subsets of an even set `S`. -/
theorem card_balanced {S : Finset (Fin k)} (hS : Even #S) :
    #(S.powerset.filter (Balanced S)) = (#S).choose (#S / 2) := by
  rw [← card_powersetCard (#S / 2) S]
  apply card_nbij' (fun U => symmDiff U (oddPts S)) (fun V => symmDiff V (oddPts S))
  · intro U hU
    simp only [mem_coe, mem_filter, mem_powerset] at hU
    simp only [mem_coe, mem_powersetCard]
    exact ⟨symmDiff_oddPts_subset hU.1, (card_oddPts hS) ▸ (balanced_iff_card hU.1).mp hU.2⟩
  · intro V hV
    simp only [mem_coe, mem_powersetCard] at hV
    simp only [mem_coe, mem_filter, mem_powerset]
    refine ⟨symmDiff_oddPts_subset hV.1, ?_⟩
    rw [balanced_iff_card (symmDiff_oddPts_subset hV.1), symmDiff_symmDiff_cancel_right,
      hV.2, card_oddPts hS]
  · intro U _; exact symmDiff_symmDiff_cancel_right _ _
  · intro V _; exact symmDiff_symmDiff_cancel_right _ _

/-- The normalized balanced subsets. -/
def repSets (S : Finset (Fin k)) : Finset (Finset (Fin k)) :=
  S.powerset.filter (fun U => Balanced S U ∧ ∀ h : S.Nonempty, S.min' h ∉ U)

theorem two_mul_card_repSets {S : Finset (Fin k)} (hS : Even #S) (hne : S.Nonempty) :
    2 * #(repSets S) = (#S).choose (#S / 2) := by
  set m := S.min' hne
  have hm : m ∈ S := S.min'_mem hne
  set B := S.powerset.filter (Balanced S)
  have hR : repSets S = B.filter (fun U => m ∉ U) := by
    ext U
    simp only [repSets, B, mem_filter, mem_powerset]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3 hne⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, fun _ => h3⟩
  have hsplit := card_filter_add_card_filter_not (s := B) (fun U => m ∉ U)
  have hbij : #(B.filter (fun U => m ∉ U)) = #(B.filter (fun U => ¬ m ∉ U)) := by
    apply card_nbij' (fun U => S \ U) (fun U => S \ U)
    · intro U hU
      simp only [B, coe_filter, mem_filter, mem_powerset, Set.mem_setOf_eq] at hU ⊢
      exact ⟨⟨sdiff_subset, balanced_sdiff hU.1.1 hS hU.1.2⟩,
        fun h => h (mem_sdiff.mpr ⟨hm, hU.2⟩)⟩
    · intro U hU
      simp only [B, coe_filter, mem_filter, mem_powerset, Set.mem_setOf_eq, not_not] at hU ⊢
      exact ⟨⟨sdiff_subset, balanced_sdiff hU.1.1 hS hU.1.2⟩, fun h => (mem_sdiff.mp h).2 hU.2⟩
    · intro U hU
      simp only [B, coe_filter, mem_filter, mem_powerset, Set.mem_setOf_eq] at hU
      exact Finset.sdiff_sdiff_eq_self hU.1.1
    · intro U hU
      simp only [B, coe_filter, mem_filter, mem_powerset, Set.mem_setOf_eq] at hU
      exact Finset.sdiff_sdiff_eq_self hU.1.1
  rw [hR, ← card_balanced hS, ← hsplit, ← hbij]
  ring

theorem card_repSets_empty : #(repSets (∅ : Finset (Fin k))) = 1 := by
  have : repSets (∅ : Finset (Fin k)) = {∅} := by
    ext U
    simp only [repSets, mem_filter, mem_powerset, subset_empty, mem_singleton]
    constructor
    · rintro ⟨h, _⟩; exact h
    · rintro rfl
      refine ⟨rfl, ?_, fun h => absurd h (by simp)⟩
      simp [Balanced]
  rw [this, card_singleton]

/-! ### Assembling the count -/

theorem fiber_eq (α : TaitColor) (S : Finset (Fin k)) :
    univ.filter (fun U => (S, U) ∈ idx k α) =
      if Even #S ∧ (S.Nonempty ∨ Even k) then repSets S else ∅ := by
  ext U
  simp only [mem_filter, mem_univ, true_and, mem_idx, realizable_iff]
  split_ifs with h
  · simp only [repSets, mem_filter, mem_powerset]
    tauto
  · simp only [Finset.notMem_empty, iff_false]
    tauto

/-- The weight of an active-set size `n`. -/
def wt (k n : ℕ) : ℕ :=
  if Even n then (if n = 0 then (if Even k then 2 else 0) else n.choose (n / 2)) else 0

theorem two_mul_card_fiber (α : TaitColor) (S : Finset (Fin k)) :
    2 * #(univ.filter (fun U => (S, U) ∈ idx k α)) = wt k #S := by
  rw [fiber_eq]
  unfold wt
  by_cases hev : Even #S
  · rw [if_pos hev]
    by_cases h0 : #S = 0
    · rw [if_pos h0]
      have hS : S = ∅ := card_eq_zero.mp h0
      subst hS
      by_cases hk : Even k
      · rw [if_pos ⟨hev, Or.inr hk⟩, if_pos hk, card_repSets_empty]
      · rw [if_neg (fun h => by
          rcases h.2 with h' | h'
          · exact absurd h' (by simp)
          · exact hk h'), if_neg hk, card_empty]
    · have hne : S.Nonempty := card_pos.mp (Nat.pos_of_ne_zero h0)
      rw [if_neg h0, if_pos ⟨hev, Or.inl hne⟩, two_mul_card_repSets hev hne]
  · rw [if_neg hev, if_neg (fun h => hev h.1), card_empty]

theorem card_idx_eq (α : TaitColor) :
    #(idx k α) = ∑ S : Finset (Fin k), #(univ.filter (fun U => (S, U) ∈ idx k α)) := by
  conv_lhs => rw [← filter_univ_mem (idx k α)]
  rw [card_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro S _
  rw [card_filter]

theorem two_mul_card_idx_nat (α : TaitColor) :
    2 * #(idx k α) = ∑ n ∈ range (k + 1), k.choose n * wt k n := by
  rw [card_idx_eq, mul_sum]
  simp_rw [two_mul_card_fiber]
  have h := sum_powerset_apply_card (fun n => wt k n) (x := (univ : Finset (Fin k)))
  rw [powerset_univ, card_univ, Fintype.card_fin] at h
  rw [h]
  simp [smul_eq_mul]

theorem wt_int (k n : ℕ) :
    (wt k n : ℤ) = (if Even n then (n.choose (n / 2) : ℤ) else 0) +
      (if n = 0 then (-1 : ℤ) ^ k else 0) := by
  unfold wt
  by_cases h0 : n = 0
  · subst h0
    have he : Even 0 := ⟨0, rfl⟩
    simp only [he, if_true, ↓reduceIte, Nat.zero_div, Nat.choose_self, Nat.cast_one]
    by_cases hk : Even k
    · rw [if_pos hk, hk.neg_one_pow]; norm_num
    · rw [if_neg hk, (Nat.not_even_iff_odd.mp hk).neg_one_pow]; norm_num
  · simp only [h0, if_false, add_zero]
    split_ifs <;> simp

theorem sum_even_reindex (k : ℕ) :
    ∑ n ∈ range (k + 1), (k.choose n : ℤ) * (if Even n then (n.choose (n / 2) : ℤ) else 0) =
      ∑ m ∈ range (k / 2 + 1), (k.choose (2 * m) : ℤ) * ((2 * m).choose m : ℤ) := by
  simp_rw [mul_ite, mul_zero]
  rw [← sum_filter]
  have himg : (range (k + 1)).filter Even = (range (k / 2 + 1)).image (fun m => 2 * m) := by
    ext n
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨h1, ⟨r, hr⟩⟩; exact ⟨r, by omega, by omega⟩
    · rintro ⟨m, hm, rfl⟩; exact ⟨by omega, ⟨m, by omega⟩⟩
  rw [himg, sum_image (fun a _ b _ h => by omega)]
  apply sum_congr rfl
  intro m _
  rw [Nat.mul_div_cancel_left m (by norm_num)]

/-- **Count.** `2 · #idx = T_k + (-1)^k`. -/
theorem two_mul_card_idx (α : TaitColor) :
    2 * (#(idx k α) : ℤ) = (centralTrinomial k : ℤ) + (-1 : ℤ) ^ k := by
  have h := two_mul_card_idx_nat (k := k) α
  have h' : (2 * #(idx k α) : ℤ) = ∑ n ∈ range (k + 1), (k.choose n : ℤ) * (wt k n : ℤ) := by
    exact_mod_cast h
  rw [h']
  simp_rw [wt_int, mul_add, sum_add_distrib, sum_even_reindex]
  unfold centralTrinomial
  push_cast
  congr 1
  simp_rw [mul_ite, mul_zero]
  rw [sum_ite_eq' (range (k + 1)) 0]
  simp

end Theorem62

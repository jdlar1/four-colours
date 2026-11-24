import Theorem62.Basic

/-!
# Lemma 2.1: unions of pairs of noncrossing matchings are exactly the balanced sets
-/

namespace Theorem62

open Finset

variable {k : ℕ}

/-- Rank of `u` in `S`: the number of elements of `S` below `u`. -/
def rank (S : Finset (Fin k)) (u : Fin k) : ℕ := #(S.filter (· < u))

/-- `U` is balanced in `S`: as many even-ranked as odd-ranked elements. -/
def Balanced (S U : Finset (Fin k)) : Prop := ∑ u ∈ U, (-1 : ℤ) ^ rank S u = 0

/-- `U` is a union of pairs of `M`. -/
def Closed {S : Finset (Fin k)} (M : NCMatching k S) (U : Finset (Fin k)) : Prop :=
  ∀ i ∈ U, M.partner i ∈ U

theorem even_card_of_invol (T : Finset (Fin k)) (p : Fin k → Fin k)
    (hmem : ∀ x ∈ T, p x ∈ T) (hne : ∀ x ∈ T, p x ≠ x) (hinv : ∀ x ∈ T, p (p x) = x) :
    Even #T := by
  have h : ∏ _x ∈ T, (-1 : ℤ) = 1 :=
    Finset.prod_involution (fun x _ => p x) (by intros; norm_num) (fun a ha _ => hne a ha)
      (fun a ha => hmem a ha) (fun a ha => hinv a ha)
  rw [prod_const] at h
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp h

/-- Inside a noncrossing matching, the elements strictly between partners are matched
among themselves. -/
theorem NCMatching.partner_between {S : Finset (Fin k)} (M : NCMatching k S) {a c : Fin k}
    (ha : a ∈ S) (hc : c ∈ S) (h1 : a < c) (h2 : c < M.partner a) :
    a < M.partner c ∧ M.partner c < M.partner a := by
  have hpc := M.mem c hc
  have hcc := M.invol c hc
  have haa := M.invol a ha
  rcases lt_trichotomy (M.partner c) a with h | h | h
  · exfalso
    exact M.noncross (M.partner c) hpc a ha ⟨h, by rw [hcc]; exact h1, by rw [hcc]; exact h2⟩
  · exfalso
    have : c = M.partner a := by rw [← hcc, h]
    exact absurd this (ne_of_lt h2)
  · refine ⟨h, ?_⟩
    rcases lt_trichotomy (M.partner c) (M.partner a) with h' | h' | h'
    · exact h'
    · exfalso
      have : c = a := by rw [← hcc, h', haa]
      exact absurd this (ne_of_gt h1)
    · exact absurd ⟨h1, h2, h'⟩ (M.noncross a ha c hc)

theorem rank_partner_of_lt {S : Finset (Fin k)} (M : NCMatching k S) {a : Fin k} (ha : a ∈ S)
    (hlt : a < M.partner a) :
    rank S (M.partner a) = rank S a + 1 + #(S.filter (fun c => a < c ∧ c < M.partner a)) := by
  unfold rank
  rw [← (S.filter (· < M.partner a)).card_filter_add_card_filter_not (fun c => c ≤ a)]
  congr 1
  · rw [Finset.filter_filter]
    have : S.filter (fun c => c < M.partner a ∧ c ≤ a) = insert a (S.filter (· < a)) := by
      ext c
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hc, -, hca⟩
        rcases eq_or_lt_of_le hca with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hc, h⟩
      · rintro (rfl | ⟨hc, h⟩)
        · exact ⟨ha, hlt, le_rfl⟩
        · exact ⟨hc, lt_trans h hlt, le_of_lt h⟩
    rw [this, card_insert_of_notMem (by simp)]
  · rw [Finset.filter_filter]
    congr 1
    ext c
    simp only [mem_filter, not_le]
    tauto

theorem neg_one_pow_rank_partner {S : Finset (Fin k)} (M : NCMatching k S) {a : Fin k}
    (ha : a ∈ S) : (-1 : ℤ) ^ rank S (M.partner a) = -(-1 : ℤ) ^ rank S a := by
  have key : ∀ a ∈ S, a < M.partner a →
      (-1 : ℤ) ^ rank S (M.partner a) = -(-1 : ℤ) ^ rank S a := by
    intro a ha hlt
    rw [rank_partner_of_lt M ha hlt]
    have hev : Even #(S.filter (fun c => a < c ∧ c < M.partner a)) := by
      apply even_card_of_invol _ M.partner
      · intro x hx
        simp only [mem_filter] at hx ⊢
        exact ⟨M.mem x hx.1, M.partner_between ha hx.1 hx.2.1 hx.2.2⟩
      · intro x hx
        exact M.ne x (mem_filter.mp hx).1
      · intro x hx
        exact M.invol x (mem_filter.mp hx).1
    rw [pow_add, pow_add, hev.neg_one_pow]
    ring
  rcases lt_or_gt_of_ne (M.ne a ha) with h | h
  · -- partner a < a
    have hpa := M.mem a ha
    have := key (M.partner a) hpa (by rw [M.invol a ha]; exact h)
    rw [M.invol a ha] at this
    rw [this]; ring
  · exact key a ha h

/-- Lemma 2.1 (⇒): a union of pairs of a noncrossing matching is balanced. -/
theorem balanced_of_closed {S : Finset (Fin k)} (M : NCMatching k S) {U : Finset (Fin k)}
    (hU : U ⊆ S) (hc : Closed M U) : Balanced S U := by
  unfold Balanced
  apply Finset.sum_involution (fun x _ => M.partner x)
  · intro a ha
    rw [neg_one_pow_rank_partner M (hU ha)]; ring
  · intro a ha _
    exact M.ne a (hU ha)
  · intro a ha
    exact hc a ha
  · intro a ha
    exact M.invol a (hU ha)

/-! ### Enumerating a finset in increasing order -/

section Enum

variable (S : Finset (Fin k))

/-- The `r`-th smallest element of `S`. -/
noncomputable def enum : Fin #S ↪o Fin k := S.orderEmbOfFin rfl

theorem enum_mem (r : Fin #S) : enum S r ∈ S := S.orderEmbOfFin_mem rfl r

theorem exists_enum {u : Fin k} (hu : u ∈ S) : ∃ r, enum S r = u := by
  have h := S.range_orderEmbOfFin rfl
  have : u ∈ Set.range (S.orderEmbOfFin rfl) := by rw [h]; exact hu
  exact this

theorem rank_enum (r : Fin #S) : rank S (enum S r) = r := by
  unfold rank
  have : S.filter (· < enum S r) = (Iio r).map (enum S).toEmbedding := by
    ext u
    simp only [mem_filter, mem_map, mem_Iio, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hu, hlt⟩
      obtain ⟨j, rfl⟩ := exists_enum S hu
      exact ⟨j, (enum S).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨enum_mem S j, (enum S).lt_iff_lt.mpr hj⟩
  rw [this, card_map, Fin.card_Iio]

theorem sum_enum {M : Type*} [AddCommMonoid M] (f : Fin k → M) :
    ∑ u ∈ S, f u = ∑ r : Fin #S, f (enum S r) := by
  conv_lhs => rw [← S.map_orderEmbOfFin_univ rfl]
  rw [sum_map]
  rfl

end Enum

/-- If `U ⊆ S` is balanced and `#S` is even and positive, two consecutive elements of `S`
are both in `U` or both outside `U`. -/
theorem exists_adjacent {S U : Finset (Fin k)} (hne : S.Nonempty) (hev : Even #S)
    (hU : U ⊆ S) (hb : Balanced S U) :
    ∃ (r : ℕ) (h : r + 1 < #S),
      (enum S ⟨r, by omega⟩ ∈ U ↔ enum S ⟨r + 1, h⟩ ∈ U) := by
  have hpos : 0 < #S := card_pos.mpr hne
  have h2 : 2 ≤ #S := by
    obtain ⟨m, hm⟩ := hev; omega
  by_contra hcon
  push_neg at hcon
  -- membership alternates
  have halt : ∀ (r : ℕ) (hr : r < #S),
      (enum S ⟨r, hr⟩ ∈ U ↔ (Even r ↔ enum S ⟨0, hpos⟩ ∈ U)) := by
    intro r
    induction r with
    | zero => intro hr; simp
    | succ r ih =>
      intro hr
      have h1 := ih (by omega)
      have h2 := hcon r hr
      rw [Nat.even_add_one]
      tauto
  -- rewrite the balance sum along the enumeration
  have hsum : ∑ u ∈ U, (-1 : ℤ) ^ rank S u =
      ∑ r : Fin #S, (if enum S r ∈ U then (-1 : ℤ) ^ (r : ℕ) else 0) := by
    have : U = S.filter (· ∈ U) := by
      ext u; simp only [mem_filter]; exact ⟨fun h => ⟨hU h, h⟩, fun h => h.2⟩
    rw [this, sum_filter, sum_enum S]
    simp only [mem_filter, rank_enum]
    apply sum_congr rfl
    intro r _
    simp [enum_mem]
  unfold Balanced at hb
  rw [hsum] at hb
  by_cases h0 : enum S ⟨0, hpos⟩ ∈ U
  · have hge : ∀ r ∈ (univ : Finset (Fin #S)),
        0 ≤ (if enum S r ∈ U then (-1 : ℤ) ^ (r : ℕ) else 0) := by
      intro r _
      have := halt r r.2
      split_ifs with h
      · have hr : Even (r : ℕ) := by tauto
        rw [hr.neg_one_pow]; norm_num
      · exact le_rfl
    have hlt : 0 < ∑ r : Fin #S, (if enum S r ∈ U then (-1 : ℤ) ^ (r : ℕ) else 0) := by
      apply lt_of_lt_of_le _ (single_le_sum hge (mem_univ ⟨0, hpos⟩))
      simp [h0]
    omega
  · have hle : ∀ r ∈ (univ : Finset (Fin #S)),
        (if enum S r ∈ U then (-1 : ℤ) ^ (r : ℕ) else 0) ≤ 0 := by
      intro r _
      have := halt r r.2
      split_ifs with h
      · have hr : ¬ Even (r : ℕ) := by tauto
        rw [Nat.not_even_iff_odd] at hr
        rw [hr.neg_one_pow]; norm_num
      · exact le_rfl
    have h1 : enum S ⟨1, by omega⟩ ∈ U := by
      have := halt 1 (by omega); simp at this; tauto
    have hlt : ∑ r : Fin #S, (if enum S r ∈ U then (-1 : ℤ) ^ (r : ℕ) else 0) < 0 := by
      have := Finset.sum_le_sum_of_subset_of_nonpos (s := {⟨1, by omega⟩})
        (t := (univ : Finset (Fin #S))) (subset_univ _) (fun i _ _ => hle i (mem_univ _))
      apply lt_of_le_of_lt this
      simp [h1]
    omega

/-- Ranks after deleting two adjacent elements `a < b` of `S`. -/
theorem rank_erase_adjacent {S : Finset (Fin k)} {a b : Fin k} (hab : a < b)
    (hadj : ∀ c ∈ S, ¬ (a < c ∧ c < b)) (ha : a ∈ S) (hb : b ∈ S) {u : Fin k} (hu : u ∈ S)
    (hua : u ≠ a) (hub : u ≠ b) :
    rank S u = rank ((S.erase a).erase b) u + (if b < u then 2 else 0) := by
  unfold rank
  rcases lt_or_gt_of_ne hua with h | h
  · have hbu : ¬ b < u := fun h' => absurd (lt_trans h (lt_trans hab h')) (lt_irrefl _)
    rw [if_neg hbu, add_zero]
    congr 1
    ext c
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨hc, hcu⟩
      exact ⟨⟨ne_of_lt (lt_trans hcu (lt_trans h hab)), ne_of_lt (lt_trans hcu h), hc⟩, hcu⟩
    · rintro ⟨⟨-, -, hc⟩, hcu⟩
      exact ⟨hc, hcu⟩
  · have hbu : b < u := by
      rcases lt_or_gt_of_ne hub with h' | h'
      · exact absurd ⟨h, h'⟩ (hadj u hu)
      · exact h'
    rw [if_pos hbu]
    have : S.filter (· < u) =
        insert a (insert b (((S.erase a).erase b).filter (· < u))) := by
      ext c
      simp only [mem_filter, mem_erase, mem_insert]
      constructor
      · rintro ⟨hc, hcu⟩
        by_cases hca : c = a
        · exact Or.inl hca
        · by_cases hcb : c = b
          · exact Or.inr (Or.inl hcb)
          · exact Or.inr (Or.inr ⟨⟨hcb, hca, hc⟩, hcu⟩)
      · rintro (rfl | rfl | ⟨⟨-, -, hc⟩, hcu⟩)
        · exact ⟨ha, h⟩
        · exact ⟨hb, hbu⟩
        · exact ⟨hc, hcu⟩
    rw [this, card_insert_of_notMem (by simp [ne_of_lt hab]), card_insert_of_notMem (by simp)]

/-- Lemma 2.1 (⇐): a balanced subset of an even set is a union of pairs of some noncrossing
perfect matching. -/
theorem exists_matching_of_balanced :
    ∀ (n : ℕ) (S U : Finset (Fin k)), #S = n → U ⊆ S → Even #S → Balanced S U →
      ∃ M : NCMatching k S, Closed M U := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S U hn hU hev hbal
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    refine ⟨⟨id, by simp, by simp, by simp, by simp⟩, ?_⟩
    intro i hi
    exact absurd (hU hi) (by simp)
  obtain ⟨r, hr, hiff⟩ := exists_adjacent hS hev hU hbal
  set a := enum S ⟨r, by omega⟩ with ha_def
  set b := enum S ⟨r + 1, hr⟩ with hb_def
  have haS : a ∈ S := enum_mem S _
  have hbS : b ∈ S := enum_mem S _
  have hab : a < b := (enum S).lt_iff_lt.mpr (by simp [Fin.lt_def])
  have hadj : ∀ c ∈ S, ¬ (a < c ∧ c < b) := by
    intro c hc ⟨h1, h2⟩
    obtain ⟨j, rfl⟩ := exists_enum S hc
    have h1' := (enum S).lt_iff_lt.mp h1
    have h2' := (enum S).lt_iff_lt.mp h2
    simp [Fin.lt_def] at h1' h2'
    omega
  have hra : rank S a = r := by rw [ha_def, rank_enum]
  have hrb : rank S b = r + 1 := by rw [hb_def, rank_enum]
  set S' := (S.erase a).erase b with hS'
  set U' := (U.erase a).erase b with hU'
  have hS'card : #S' = #S - 2 := by
    rw [hS', card_erase_of_mem (by simp [ne_of_gt hab, hbS]), card_erase_of_mem haS]; omega
  have hU'S' : U' ⊆ S' := by
    intro x hx
    simp only [hU', hS', mem_erase] at hx ⊢
    exact ⟨hx.1, hx.2.1, hU hx.2.2⟩
  have hev' : Even #S' := by
    rw [hS'card]; obtain ⟨m, hm⟩ := hev
    exact ⟨m - 1, by omega⟩
  have hbal' : Balanced S' U' := by
    unfold Balanced at hbal ⊢
    have hU'eq : ∑ u ∈ U', (-1 : ℤ) ^ rank S' u = ∑ u ∈ U', (-1 : ℤ) ^ rank S u := by
      apply sum_congr rfl
      intro u hu
      simp only [hU', mem_erase] at hu
      rw [rank_erase_adjacent hab hadj haS hbS (hU hu.2.2) hu.2.1 hu.1, pow_add]
      split_ifs <;> simp [hS']
    rw [hU'eq]
    by_cases haU : a ∈ U
    · have hbU : b ∈ U := hiff.mp haU
      have : U = insert a (insert b U') := by
        ext x; simp only [hU', mem_insert, mem_erase]
        constructor
        · intro hx; tauto
        · rintro (rfl | rfl | ⟨-, -, hx⟩) <;> assumption
      rw [this, sum_insert (by simp [hU', ne_of_lt hab]), sum_insert (by simp [hU'])] at hbal
      rw [hra, hrb, pow_succ] at hbal
      linarith
    · have hbU : b ∉ U := fun h => haU (hiff.mpr h)
      have : U' = U := by
        rw [hU', erase_eq_of_notMem haU, erase_eq_of_notMem hbU]
      rw [this]; exact hbal
  have hlt : #S' < n := by
    have : 0 < #S := card_pos.mpr hS
    omega
  obtain ⟨M', hM'⟩ := ih #S' hlt S' U' rfl hU'S' hev' hbal'
  have hS'mem : ∀ x, x ∈ S' ↔ x ∈ S ∧ x ≠ a ∧ x ≠ b := by
    intro x; simp only [hS', mem_erase]; tauto
  let p : Fin k → Fin k := fun x => if x = a then b else if x = b then a else M'.partner x
  have hp_a : p a = b := by simp [p]
  have hp_b : p b = a := by simp [p, ne_of_gt hab]
  have hp_o : ∀ x, x ≠ a → x ≠ b → p x = M'.partner x := by
    intro x h1 h2; simp [p, h1, h2]
  have hM'mem : ∀ x ∈ S', M'.partner x ∈ S' := M'.mem
  refine ⟨⟨p, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    by_cases h1 : x = a
    · subst h1; rw [hp_a]; exact hbS
    by_cases h2 : x = b
    · subst h2; rw [hp_b]; exact haS
    rw [hp_o x h1 h2]
    exact ((hS'mem _).mp (hM'mem x ((hS'mem x).mpr ⟨hx, h1, h2⟩))).1
  · intro x hx
    by_cases h1 : x = a
    · subst h1; rw [hp_a]; exact ne_of_gt hab
    by_cases h2 : x = b
    · subst h2; rw [hp_b]; exact ne_of_lt hab
    rw [hp_o x h1 h2]
    exact M'.ne x ((hS'mem x).mpr ⟨hx, h1, h2⟩)
  · intro x hx
    by_cases h1 : x = a
    · subst h1; rw [hp_a, hp_b]
    by_cases h2 : x = b
    · subst h2; rw [hp_b, hp_a]
    have hx' : x ∈ S' := (hS'mem x).mpr ⟨hx, h1, h2⟩
    have hy := (hS'mem _).mp (hM'mem x hx')
    rw [hp_o x h1 h2, hp_o _ hy.2.1 hy.2.2, M'.invol x hx']
  · intro x hx y hy ⟨h1, h2, h3⟩
    by_cases hxa : x = a
    · subst hxa; rw [hp_a] at h2; exact hadj y hy ⟨h1, h2⟩
    by_cases hxb : x = b
    · subst hxb; rw [hp_b] at h2; exact absurd (lt_trans h1 h2) (not_lt.mpr (le_of_lt hab))
    have hx' : x ∈ S' := (hS'mem x).mpr ⟨hx, hxa, hxb⟩
    have hpx := (hS'mem _).mp (hM'mem x hx')
    rw [hp_o x hxa hxb] at h2 h3
    by_cases hya : y = a
    · subst hya; rw [hp_a] at h3; exact hadj _ hpx.1 ⟨h2, h3⟩
    by_cases hyb : y = b
    · subst hyb; rw [hp_b] at h3; exact absurd (lt_trans h2 h3) (not_lt.mpr (le_of_lt hab))
    have hy' : y ∈ S' := (hS'mem y).mpr ⟨hy, hya, hyb⟩
    rw [hp_o y hya hyb] at h3
    exact M'.noncross x hx' y hy' ⟨h1, h2, h3⟩
  · intro i hi
    show p i ∈ U
    by_cases h1 : i = a
    · subst h1; rw [hp_a]; exact hiff.mp hi
    by_cases h2 : i = b
    · subst h2; rw [hp_b]; exact hiff.mpr hi
    rw [hp_o i h1 h2]
    have hi' : i ∈ U' := by simp only [hU', mem_erase]; exact ⟨h2, h1, hi⟩
    have := hM' i hi'
    simp only [hU', mem_erase] at this
    exact this.2.2

end Theorem62

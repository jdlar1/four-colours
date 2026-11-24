import Theorem62.Matching

/-!
# Fourier description of Kempe blocks (Lemma 2.2)

For a colour `α` we fix another colour `b = other α` and the sign `sgn t i = ±1` telling the two
non-`α` colours apart. `chi U t = ∏_{i ∈ U} sgn t i` and `fS S U = [sector = S] · chi U`.
-/

namespace Theorem62

open Finset

variable {k : ℕ}

/-- The sign character of 𝔽₂² with kernel `{0, b}`. -/
def psi (b x : F22) : K := if x = 0 ∨ x = b then 1 else -1

theorem psi_add {b : F22} (hb : b ≠ 0) (x y : F22) : psi b (x + y) = psi b x * psi b y := by
  have key : ∀ b x y : F22, b ≠ 0 →
      ((x + y = 0 ∨ x + y = b) ↔ ((x = 0 ∨ x = b) ↔ (y = 0 ∨ y = b))) := by decide
  have h := key b x y hb
  unfold psi
  split_ifs <;> norm_num <;> tauto

theorem psi_sq (b x : F22) : psi b x * psi b x = 1 := by
  unfold psi; split_ifs <;> norm_num

theorem psi_ne_zero (b x : F22) : psi b x ≠ 0 := by
  unfold psi; split_ifs <;> norm_num

theorem psi_zero (b : F22) : psi b 0 = 1 := by simp [psi]

theorem psi_of_ne {b x : F22} (h0 : x ≠ 0) (hb : x ≠ b) : psi b x = -1 := by
  simp [psi, h0, hb]

theorem prod_psi {b : F22} (hb : b ≠ 0) (s : Finset (Fin k)) (f : Fin k → F22) :
    ∏ i ∈ s, psi b (f i) = psi b (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp [psi_zero]
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, psi_add hb, ih]

/-- A fixed Tait colour different from `α`. -/
def other (α : TaitColor) : TaitColor :=
  if α.1 = (1, 0) then ⟨(0, 1), by decide⟩ else ⟨(1, 0), by decide⟩

theorem other_ne (α : TaitColor) : (other α).1 ≠ α.1 := by
  revert α; decide

theorem F22_swap_fact : ∀ a x y : F22, a ≠ 0 → x ≠ 0 → y ≠ 0 → x ≠ a → y ≠ a → x ≠ y →
    y = x + a := by decide

theorem F22_add_ne : ∀ a x : F22, x ≠ 0 → x ≠ a → x + a ≠ 0 ∧ x + a ≠ a := by decide

section Sgn

variable (α : TaitColor)

/-- `sgn α t i = ±1` distinguishes the two non-`α` colours (and is `-1` on `α`). -/
def sgn (t : TaitWord k) (i : Fin k) : K := psi (other α).1 (t.1 i).1

/-- Characters `chi U t = ∏_{i ∈ U} sgn t i`. -/
def chi (U : Finset (Fin k)) (t : TaitWord k) : K := ∏ i ∈ U, sgn α t i

/-- The character `chi U`, restricted to the words with active set `S`. -/
def fS (S U : Finset (Fin k)) (t : TaitWord k) : K := if sector α t = S then chi α U t else 0

variable {α}

theorem sgn_sq (t : TaitWord k) (i : Fin k) : sgn α t i * sgn α t i = 1 := psi_sq _ _

theorem sgn_ne_zero (t : TaitWord k) (i : Fin k) : sgn α t i ≠ 0 := psi_ne_zero _ _

theorem mem_sector {t : TaitWord k} {i : Fin k} : i ∈ sector α t ↔ t.1 i ≠ α := by
  simp [sector]

theorem val_ne_of_mem_sector {t : TaitWord k} {i : Fin k} (h : i ∈ sector α t) :
    (t.1 i).1 ≠ α.1 := by
  intro h'; exact mem_sector.mp h (Subtype.ext h')

/-- Swapping the two non-`α` colours flips the sign. -/
theorem sgn_flip {t t' : TaitWord k} {i : Fin k} (hi : (t.1 i).1 ≠ α.1)
    (h : (t'.1 i).1 = (t.1 i).1 + α.1) : sgn α t' i = -sgn α t i := by
  unfold sgn
  rw [h, psi_add (other α).2, psi_of_ne α.2 (other_ne α).symm]
  ring

theorem chi_eq_prod_ite (U : Finset (Fin k)) (t : TaitWord k) :
    chi α U t = ∏ i, if i ∈ U then sgn α t i else 1 := by
  rw [prod_ite_mem, univ_inter]; rfl

theorem chi_mul (U U' : Finset (Fin k)) (t : TaitWord k) :
    chi α U t * chi α U' t = chi α (symmDiff U U') t := by
  rw [chi_eq_prod_ite, chi_eq_prod_ite, chi_eq_prod_ite, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  by_cases h1 : i ∈ U <;> by_cases h2 : i ∈ U' <;> simp [h1, h2, sgn_sq, mem_symmDiff]

theorem chi_sq (U : Finset (Fin k)) (t : TaitWord k) : chi α U t * chi α U t = 1 := by
  rw [chi_mul, symmDiff_self]; simp [chi]

/-- On a Tait word, `chi (sector)` is the constant sign `(-1)^(k - #sector)`. -/
theorem chi_sector (t : TaitWord k) :
    chi α (sector α t) t = (-1) ^ #(sector α t)ᶜ := by
  have htot : ∏ i, sgn α t i = 1 := by
    unfold sgn
    rw [prod_psi (other α).2, t.2, psi_zero]
  rw [← prod_mul_prod_compl (sector α t)] at htot
  have hc : ∏ i ∈ (sector α t)ᶜ, sgn α t i = (-1) ^ #(sector α t)ᶜ := by
    rw [← prod_const]
    apply prod_congr rfl
    intro i hi
    have : t.1 i = α := by
      rw [mem_compl, mem_sector, not_not] at hi; exact hi
    unfold sgn
    rw [this]
    exact psi_of_ne α.2 (other_ne α).symm
  rw [hc] at htot
  have h2 : ((-1 : K) ^ #(sector α t)ᶜ) * (-1) ^ #(sector α t)ᶜ = 1 := by
    rw [← mul_pow]; norm_num
  calc chi α (sector α t) t
      = chi α (sector α t) t * ((-1) ^ #(sector α t)ᶜ * (-1) ^ #(sector α t)ᶜ) := by
        rw [h2, mul_one]
    _ = (-1) ^ #(sector α t)ᶜ := by unfold chi; rw [← mul_assoc, htot, one_mul]

/-- The active set of a Tait word has even size. -/
theorem even_card_sector (t : TaitWord k) : Even #(sector α t) := by
  have htot : ∏ i, psi α.1 (t.1 i).1 = 1 := by
    rw [prod_psi α.2, t.2, psi_zero]
  rw [← prod_filter_mul_prod_filter_not univ (fun i => t.1 i ≠ α)] at htot
  have h1 : ∏ i ∈ univ.filter (fun i => t.1 i ≠ α), psi α.1 (t.1 i).1 =
      (-1) ^ #(sector α t) := by
    rw [← prod_const]
    unfold sector
    apply prod_congr rfl
    intro i hi
    rw [mem_filter] at hi
    exact psi_of_ne (t.1 i).2 (fun h => hi.2 (Subtype.ext h))
  have h2 : ∏ i ∈ univ.filter (fun i => ¬ t.1 i ≠ α), psi α.1 (t.1 i).1 = 1 := by
    apply prod_eq_one
    intro i hi
    rw [mem_filter, not_not] at hi
    simp [psi, hi.2]
  rw [h1, h2, mul_one] at htot
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp htot

end Sgn

section Blocks

variable {α : TaitColor}

theorem sgn_cases (t : TaitWord k) (i : Fin k) : sgn α t i = 1 ∨ sgn α t i = -1 := by
  unfold sgn psi; split_ifs <;> simp

theorem chi_ne_zero (U : Finset (Fin k)) (t : TaitWord k) : chi α U t ≠ 0 := by
  intro h; have := chi_sq (α := α) U t; rw [h, zero_mul] at this; exact zero_ne_one this

/-- On a position where both words avoid `α`, they agree iff their signs agree. -/
theorem eq_iff_sgn_eq {t t' : TaitWord k} {i : Fin k} (h : (t.1 i).1 ≠ α.1)
    (h' : (t'.1 i).1 ≠ α.1) : t'.1 i = t.1 i ↔ sgn α t' i = sgn α t i := by
  constructor
  · intro e; simp [sgn, e]
  · intro e
    by_contra hne
    have hv : (t'.1 i).1 = (t.1 i).1 + α.1 :=
      F22_swap_fact α.1 (t.1 i).1 (t'.1 i).1 α.2 (t.1 i).2 (t'.1 i).2 h h'
        (fun e' => hne (Subtype.ext e'.symm))
    rw [sgn_flip h hv] at e
    exact sgn_ne_zero t i (by linarith)

/-- The pair sign `sgn t a * sgn t (partner a)`. -/
def pairSgn (α : TaitColor) {S : Finset (Fin k)} (M : NCMatching k S) (t : TaitWord k)
    (a : Fin k) : K :=
  sgn α t a * sgn α t (M.partner a)

/-- **Block characterization.** -/
theorem mem_kempeBlock_iff {S : Finset (Fin k)} (M : NCMatching k S) {t : TaitWord k}
    (hS : sector α t = S) (t' : TaitWord k) :
    t' ∈ kempeBlock α t M ↔ sector α t' = S ∧ ∀ a ∈ S, pairSgn α M t' a = pairSgn α M t a := by
  constructor
  · rintro ⟨A, hAS, hAc, hA⟩
    have hsgn : ∀ i, sgn α t' i = if i ∈ A then -sgn α t i else sgn α t i := by
      intro i
      split_ifs with hi
      · exact sgn_flip (val_ne_of_mem_sector (hS ▸ hAS hi)) (by rw [hA i, if_pos hi])
      · unfold sgn; rw [hA i, if_neg hi]
    refine ⟨?_, ?_⟩
    · ext i
      rw [← hS, mem_sector, mem_sector]
      by_cases hi : i ∈ A
      · have hiS : (t.1 i).1 ≠ α.1 := val_ne_of_mem_sector (hS ▸ hAS hi)
        have h1 := hA i
        rw [if_pos hi] at h1
        have hne := (F22_add_ne α.1 (t.1 i).1 (t.1 i).2 hiS).2
        constructor
        · intro _ e; exact hiS (congrArg Subtype.val e)
        · intro _ e; exact hne (h1 ▸ congrArg Subtype.val e)
      · have h1 := hA i
        rw [if_neg hi] at h1
        have : t'.1 i = t.1 i := Subtype.ext h1
        rw [this]
    · intro a ha
      have hpa : M.partner a ∈ A ↔ a ∈ A := by
        constructor
        · intro h; have := hAc _ h; rwa [M.invol a ha] at this
        · exact hAc a
      unfold pairSgn
      rw [hsgn a, hsgn (M.partner a)]
      by_cases h : a ∈ A
      · rw [if_pos h, if_pos (hpa.mpr h)]; ring
      · rw [if_neg h, if_neg (fun h' => h (hpa.mp h'))]
  · rintro ⟨hS', hpair⟩
    refine ⟨S.filter (fun i => t'.1 i ≠ t.1 i), filter_subset _ _, ?_, ?_⟩
    · intro i hi
      rw [mem_filter] at hi ⊢
      refine ⟨M.mem i hi.1, ?_⟩
      have hi1 : (t.1 i).1 ≠ α.1 := val_ne_of_mem_sector (hS ▸ hi.1)
      have hi2 : (t'.1 i).1 ≠ α.1 := val_ne_of_mem_sector (hS' ▸ hi.1)
      have hp := M.mem i hi.1
      have hp1 : (t.1 (M.partner i)).1 ≠ α.1 := val_ne_of_mem_sector (hS ▸ hp)
      have hp2 : (t'.1 (M.partner i)).1 ≠ α.1 := val_ne_of_mem_sector (hS' ▸ hp)
      intro e
      rw [eq_iff_sgn_eq hp1 hp2] at e
      have h := hpair i hi.1
      unfold pairSgn at h
      rw [e] at h
      have h2 : sgn α t' i = sgn α t i := mul_right_cancel₀ (sgn_ne_zero t (M.partner i)) h
      exact hi.2 ((eq_iff_sgn_eq hi1 hi2).mpr h2)
    · intro i
      split_ifs with hi
      · rw [mem_filter] at hi
        exact F22_swap_fact α.1 (t.1 i).1 (t'.1 i).1 α.2 (t.1 i).2 (t'.1 i).2
          (val_ne_of_mem_sector (hS ▸ hi.1)) (val_ne_of_mem_sector (hS' ▸ hi.1))
          (fun e => hi.2 (Subtype.ext e.symm))
      · by_cases hiS : i ∈ S
        · have : t'.1 i = t.1 i := by
            by_contra hne; exact hi (mem_filter.mpr ⟨hiS, hne⟩)
          rw [this]
        · have h1 : t.1 i = α := by
            have := hiS; rw [← hS, mem_sector, not_not] at this; exact this
          have h2 : t'.1 i = α := by
            have := hiS; rw [← hS', mem_sector, not_not] at this; exact this
          rw [h1, h2]

/-- Characters of `M`-closed sets are constant on blocks. -/
theorem chi_eq_of_pairSgn {S U : Finset (Fin k)} (M : NCMatching k S) (hU : U ⊆ S)
    (hc : Closed M U) {t t' : TaitWord k} (h : ∀ a ∈ S, pairSgn α M t' a = pairSgn α M t a) :
    chi α U t' = chi α U t := by
  have hprod : chi α U t' * chi α U t = 1 := by
    unfold chi
    rw [← prod_mul_distrib]
    refine Finset.prod_involution (fun a _ => M.partner a) ?_ (fun a ha _ => M.ne a (hU ha))
      (fun a ha => hc a ha) (fun a ha => M.invol a (hU ha))
    intro a ha
    have h1 := h a (hU ha)
    unfold pairSgn at h1
    calc sgn α t' a * sgn α t a * (sgn α t' (M.partner a) * sgn α t (M.partner a))
        = (sgn α t' a * sgn α t' (M.partner a)) * (sgn α t a * sgn α t (M.partner a)) := by ring
      _ = (sgn α t a * sgn α t (M.partner a)) * (sgn α t a * sgn α t (M.partner a)) := by rw [h1]
      _ = (sgn α t a * sgn α t a) * (sgn α t (M.partner a) * sgn α t (M.partner a)) := by ring
      _ = 1 := by rw [sgn_sq, sgn_sq, one_mul]
  have h2 := chi_sq (α := α) U t
  exact mul_right_cancel₀ (chi_ne_zero U t) (hprod.trans h2.symm)

end Blocks

section Span

variable {α : TaitColor}

theorem pairSgn_cases {S : Finset (Fin k)} (M : NCMatching k S) (t : TaitWord k) (a : Fin k) :
    pairSgn α M t a = 1 ∨ pairSgn α M t a = -1 := by
  unfold pairSgn
  rcases sgn_cases (α := α) t a with h | h <;> rcases sgn_cases (α := α) t (M.partner a) with h' | h' <;>
    simp [h, h']

theorem ite_eq_half {x c : K} (hx : x = 1 ∨ x = -1) (hc : c = 1 ∨ c = -1) :
    (if x = c then (1 : K) else 0) = c / 2 * x + 1 / 2 := by
  rcases hx with rfl | rfl <;> rcases hc with rfl | rfl <;> norm_num

/-- The points `a` with `a < partner a`: one representative per pair. -/
def lowPts {S : Finset (Fin k)} (M : NCMatching k S) : Finset (Fin k) :=
  S.filter (fun a => a < M.partner a)

theorem lowPts_subset {S : Finset (Fin k)} (M : NCMatching k S) : lowPts M ⊆ S :=
  filter_subset _ _

theorem union_image_subset {S Q : Finset (Fin k)} (M : NCMatching k S) (hQ : Q ⊆ lowPts M) :
    Q ∪ Q.image M.partner ⊆ S := by
  intro x hx
  rw [mem_union, mem_image] at hx
  rcases hx with hx | ⟨a, ha, rfl⟩
  · exact lowPts_subset M (hQ hx)
  · exact M.mem a (lowPts_subset M (hQ ha))

theorem union_image_closed {S Q : Finset (Fin k)} (M : NCMatching k S) (hQ : Q ⊆ lowPts M) :
    Closed M (Q ∪ Q.image M.partner) := by
  intro x hx
  rw [mem_union, mem_image] at hx ⊢
  rcases hx with hx | ⟨a, ha, rfl⟩
  · exact Or.inr ⟨x, hx, rfl⟩
  · left; rw [M.invol a (lowPts_subset M (hQ ha))]; exact ha

theorem chi_union_image {S Q : Finset (Fin k)} (M : NCMatching k S) (hQ : Q ⊆ lowPts M)
    (t : TaitWord k) : chi α (Q ∪ Q.image M.partner) t = ∏ a ∈ Q, pairSgn α M t a := by
  have hS : ∀ a ∈ Q, a ∈ S ∧ a < M.partner a := fun a ha => by
    have := hQ ha; unfold lowPts at this; rw [mem_filter] at this; exact this
  have hdisj : Disjoint Q (Q.image M.partner) := by
    rw [disjoint_left]
    intro a ha hb
    rw [mem_image] at hb
    obtain ⟨b, hb, rfl⟩ := hb
    have h1 := (hS b hb).2
    have h2 := (hS _ ha).2
    rw [M.invol b (hS b hb).1] at h2
    exact lt_asymm h1 h2
  have hinj : Set.InjOn M.partner Q := by
    intro a ha b hb hab
    have := congrArg M.partner hab
    rwa [M.invol a (hS a ha).1, M.invol b (hS b hb).1] at this
  unfold chi pairSgn
  rw [prod_union hdisj, prod_image hinj, prod_mul_distrib]

/-- The Balanced Fourier functions: `fS S U` with `S` an active set and `U ⊆ S` balanced. -/
def fourierSet (k : ℕ) (α : TaitColor) : Set (TaitWord k → K) :=
  {f | ∃ S U, (∃ t : TaitWord k, sector α t = S) ∧ U ⊆ S ∧ Balanced S U ∧ f = fS α S U}

theorem forall_S_iff_lowPts {S : Finset (Fin k)} (M : NCMatching k S) (t t' : TaitWord k) :
    (∀ a ∈ S, pairSgn α M t' a = pairSgn α M t a) ↔
      ∀ a ∈ lowPts M, pairSgn α M t' a = pairSgn α M t a := by
  constructor
  · intro h a ha; exact h a (lowPts_subset M ha)
  · intro h a ha
    rcases lt_or_gt_of_ne (M.ne a ha).symm with hlt | hlt
    · exact h a (mem_filter.mpr ⟨ha, hlt⟩)
    · have hp : M.partner a ∈ lowPts M := by
        refine mem_filter.mpr ⟨M.mem a ha, ?_⟩
        rw [M.invol a ha]; exact hlt
      have := h _ hp
      unfold pairSgn at this ⊢
      rw [M.invol a ha] at this
      rw [mul_comm, this, mul_comm]

/-- **Upper bound:** a block indicator is a combination of characters of closed sets. -/
theorem blockInd_eq_sum {S : Finset (Fin k)} (M : NCMatching k S) {t : TaitWord k}
    (hS : sector α t = S) :
    (kempeBlock α t M).indicator (fun _ => (1 : K)) =
      ∑ Q ∈ (lowPts M).powerset,
        ((∏ a ∈ Q, pairSgn α M t a / 2) * (1 / 2 : K) ^ #(lowPts M \ Q)) •
          fS α S (Q ∪ Q.image M.partner) := by
  classical
  funext t'
  rw [Set.indicator_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hmem := mem_kempeBlock_iff M hS t'
  by_cases ht' : sector α t' = S
  · have hR : ∀ Q ∈ (lowPts M).powerset,
        ((∏ a ∈ Q, pairSgn α M t a / 2) * (1 / 2 : K) ^ #(lowPts M \ Q)) *
          fS α S (Q ∪ Q.image M.partner) t' =
        (∏ a ∈ Q, pairSgn α M t a / 2 * pairSgn α M t' a) * ∏ a ∈ lowPts M \ Q, (1 / 2 : K) := by
      intro Q hQ
      rw [mem_powerset] at hQ
      unfold fS
      rw [if_pos ht', chi_union_image M hQ, prod_const, prod_mul_distrib]
      ring
    have hiff : t' ∈ kempeBlock α t M ↔ ∀ a ∈ lowPts M, pairSgn α M t' a = pairSgn α M t a := by
      rw [hmem, ← forall_S_iff_lowPts M t t']
      simp [ht']
    rw [sum_congr rfl hR, ← prod_add,
      prod_congr rfl (fun a _ => (ite_eq_half (pairSgn_cases M t' a) (pairSgn_cases M t a)).symm),
      prod_boole]
    by_cases h : t' ∈ kempeBlock α t M
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  · rw [if_neg (fun h => ht' (hmem.mp h).1)]
    symm
    apply sum_eq_zero
    intro Q _
    unfold fS
    rw [if_neg ht', mul_zero]

theorem blockInd_mem_fourier (t : TaitWord k) (M : NCMatching k (sector α t)) :
    (kempeBlock α t M).indicator (fun _ => (1 : K)) ∈ Submodule.span K (fourierSet k α) := by
  rw [blockInd_eq_sum M rfl]
  apply Submodule.sum_mem
  intro Q hQ
  apply Submodule.smul_mem
  apply Submodule.subset_span
  rw [mem_powerset] at hQ
  exact ⟨sector α t, _, ⟨t, rfl⟩, union_image_subset M hQ,
    balanced_of_closed M (union_image_subset M hQ) (union_image_closed M hQ), rfl⟩

theorem blockInd_mem_kempeSpan {S : Finset (Fin k)} {t : TaitWord k} (hS : sector α t = S)
    (M : NCMatching k S) :
    (kempeBlock α t M).indicator (fun _ => (1 : K)) ∈ kempeSpan k α := by
  subst hS
  exact Submodule.subset_span ⟨t, M, rfl⟩

/-- The block of `t` as a finset (via the characterization). -/
def blockF (α : TaitColor) {S : Finset (Fin k)} (M : NCMatching k S) (t : TaitWord k) :
    Finset (TaitWord k) :=
  univ.filter (fun t' => sector α t' = S ∧ ∀ a ∈ S, pairSgn α M t' a = pairSgn α M t a)

/-- **Lower bound (averaging):** characters of closed sets are combinations of blocks. -/
theorem fS_eq_sum_blocks {S U : Finset (Fin k)} (M : NCMatching k S) (hU : U ⊆ S)
    (hc : Closed M U) :
    fS α S U = ∑ t ∈ univ.filter (fun t : TaitWord k => sector α t = S),
      (chi α U t / #(blockF α M t)) • (kempeBlock α t M).indicator (fun _ => (1 : K)) := by
  classical
  funext t'
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hind : ∀ t ∈ univ.filter (fun t : TaitWord k => sector α t = S),
      chi α U t / #(blockF α M t) * (kempeBlock α t M).indicator (fun _ => (1 : K)) t' =
        if t' ∈ blockF α M t then chi α U t / #(blockF α M t) else 0 := by
    intro t ht
    rw [mem_filter] at ht
    rw [Set.indicator_apply]
    have := mem_kempeBlock_iff M ht.2 t'
    by_cases h : t' ∈ kempeBlock α t M
    · rw [if_pos h, if_pos (show t' ∈ blockF α M t from mem_filter.mpr ⟨mem_univ _, this.mp h⟩),
        mul_one]
    · rw [if_neg h, if_neg (fun h' : t' ∈ blockF α M t => h (this.mpr (mem_filter.mp h').2)),
        mul_zero]
  rw [sum_congr rfl hind]
  by_cases ht' : sector α t' = S
  · have key : ∀ t ∈ univ.filter (fun t : TaitWord k => sector α t = S),
        (if t' ∈ blockF α M t then chi α U t / #(blockF α M t) else 0) =
          if t ∈ blockF α M t' then chi α U t' / #(blockF α M t') else 0 := by
      intro t ht
      rw [mem_filter] at ht
      have hiff : t' ∈ blockF α M t ↔ t ∈ blockF α M t' := by
        simp only [blockF, mem_filter, mem_univ, true_and, ht', ht.2]
        exact ⟨fun h a ha => (h a ha).symm, fun h a ha => (h a ha).symm⟩
      by_cases hm : t ∈ blockF α M t'
      · rw [if_pos (hiff.mpr hm), if_pos hm]
        have hp : ∀ a ∈ S, pairSgn α M t a = pairSgn α M t' a := (mem_filter.mp hm).2.2
        have hblk : blockF α M t = blockF α M t' := by
          ext x
          simp only [blockF, mem_filter, mem_univ, true_and]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, fun a ha => (h2 a ha).trans (hp a ha)⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, fun a ha => (h2 a ha).trans (hp a ha).symm⟩
        rw [hblk, chi_eq_of_pairSgn M hU hc hp]
      · rw [if_neg (fun h => hm (hiff.mp h)), if_neg hm]
    rw [sum_congr rfl key, ← sum_filter]
    have hsub : (univ.filter (fun t : TaitWord k => sector α t = S)).filter
        (fun t => t ∈ blockF α M t') = blockF α M t' := by
      ext x
      simp only [mem_filter, mem_univ, true_and, blockF]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨h.1, h⟩
    rw [hsub, sum_const, nsmul_eq_mul]
    have hne : (#(blockF α M t') : K) ≠ 0 := by
      have : t' ∈ blockF α M t' := mem_filter.mpr ⟨mem_univ _, ht', fun _ _ => rfl⟩
      exact_mod_cast (card_pos.mpr ⟨t', this⟩).ne'
    unfold fS
    rw [if_pos ht']
    field_simp
  · unfold fS
    rw [if_neg ht']
    symm
    apply sum_eq_zero
    intro t ht
    rw [mem_filter] at ht
    rw [if_neg]
    intro h
    exact ht' (mem_filter.mp h).2.1

/-- **Lemma 2.2.** The literal Kempe span is the span of the balanced Fourier functions. -/
theorem kempeSpan_eq_fourier (k : ℕ) (α : TaitColor) :
    kempeSpan k α = Submodule.span K (fourierSet k α) := by
  apply le_antisymm
  · rw [kempeSpan, Submodule.span_le]
    rintro f ⟨t, M, rfl⟩
    exact blockInd_mem_fourier t M
  · rw [Submodule.span_le]
    rintro f ⟨S, U, ⟨t0, ht0⟩, hUS, hbal, rfl⟩
    obtain ⟨M, hM⟩ := exists_matching_of_balanced #S S U rfl hUS
      (ht0 ▸ even_card_sector t0) hbal
    rw [fS_eq_sum_blocks M hUS hM]
    apply Submodule.sum_mem
    intro t ht
    rw [mem_filter] at ht
    exact Submodule.smul_mem _ _ (blockInd_mem_kempeSpan ht.2 M)

end Span

section Flip

variable {α : TaitColor}

/-- Swap the two non-`α` colours, fixing `α`. -/
def swapc (α x : TaitColor) : TaitColor :=
  if h : x = α then α else ⟨x.1 + α.1, (F22_add_ne α.1 x.1 x.2 (fun e => h (Subtype.ext e))).1⟩

theorem swapc_val {x : TaitColor} (h : x ≠ α) : (swapc α x).1 = x.1 + α.1 := by
  simp [swapc, h]

theorem swapc_ne {x : TaitColor} (h : x ≠ α) : swapc α x ≠ α := by
  intro e
  have := congrArg Subtype.val e
  rw [swapc_val h] at this
  exact (F22_add_ne α.1 x.1 x.2 (fun e => h (Subtype.ext e))).2 this

theorem swapc_swapc {x : TaitColor} (h : x ≠ α) : swapc α (swapc α x) = x := by
  apply Subtype.ext
  rw [swapc_val (swapc_ne h), swapc_val h, add_assoc, F22_add_self, add_zero]

/-- Swap the non-`α` colours at the two positions `i`, `j`. -/
def flipFun (α : TaitColor) (i j : Fin k) (t : Fin k → TaitColor) : Fin k → TaitColor :=
  fun l => if l = i ∨ l = j then swapc α (t l) else t l

theorem flipFun_sum {t : Fin k → TaitColor} {i j : Fin k} (hi : t i ≠ α) (hj : t j ≠ α)
    (hij : i ≠ j) : ∑ l, (flipFun α i j t l).1 = ∑ l, (t l).1 := by
  have h : ∀ l, (flipFun α i j t l).1 =
      (t l).1 + ((if l = i then α.1 else 0) + (if l = j then α.1 else 0)) := by
    intro l
    unfold flipFun
    by_cases h1 : l = i
    · subst h1; simp [hij, swapc_val hi]
    · by_cases h2 : l = j
      · subst h2; simp [h1, swapc_val hj]
      · simp [h1, h2]
  rw [sum_congr rfl (fun l _ => h l), sum_add_distrib, sum_add_distrib]
  simp [F22_add_self]

/-- The involution on words used for orthogonality. -/
def flipW (α : TaitColor) (i j : Fin k) (t : TaitWord k) : TaitWord k :=
  if h : t.1 i ≠ α ∧ t.1 j ≠ α ∧ i ≠ j then
    ⟨flipFun α i j t.1, (flipFun_sum h.1 h.2.1 h.2.2).trans t.2⟩
  else t

theorem flipW_val {t : TaitWord k} {i j : Fin k} (h : t.1 i ≠ α ∧ t.1 j ≠ α ∧ i ≠ j) :
    (flipW α i j t).1 = flipFun α i j t.1 := by
  simp [flipW, h]

theorem flipW_cond {t : TaitWord k} {i j : Fin k} (h : t.1 i ≠ α ∧ t.1 j ≠ α ∧ i ≠ j) :
    (flipW α i j t).1 i ≠ α ∧ (flipW α i j t).1 j ≠ α ∧ i ≠ j := by
  rw [flipW_val h]
  unfold flipFun
  simp only [true_or, or_true, if_true]
  exact ⟨swapc_ne h.1, swapc_ne h.2.1, h.2.2⟩

theorem flipW_flipW (i j : Fin k) (t : TaitWord k) : flipW α i j (flipW α i j t) = t := by
  by_cases h : t.1 i ≠ α ∧ t.1 j ≠ α ∧ i ≠ j
  · apply Subtype.ext
    rw [flipW_val (flipW_cond h)]
    funext l
    unfold flipFun
    rw [flipW_val h]
    unfold flipFun
    by_cases hl : l = i ∨ l = j
    · rw [if_pos hl, if_pos hl]
      rcases hl with rfl | rfl
      · exact swapc_swapc h.1
      · exact swapc_swapc h.2.1
    · rw [if_neg hl, if_neg hl]
  · simp [flipW, h]

theorem sector_flipW (i j : Fin k) (t : TaitWord k) : sector α (flipW α i j t) = sector α t := by
  by_cases h : t.1 i ≠ α ∧ t.1 j ≠ α ∧ i ≠ j
  · ext l
    rw [mem_sector, mem_sector, flipW_val h]
    unfold flipFun
    by_cases hl : l = i ∨ l = j
    · rw [if_pos hl]
      have hl' : t.1 l ≠ α := by rcases hl with rfl | rfl; exacts [h.1, h.2.1]
      simp only [ne_eq, swapc_ne hl', hl', not_false_eq_true]
    · rw [if_neg hl]
  · simp [flipW, h]

theorem sgn_flipW {t : TaitWord k} {i j : Fin k} (h : t.1 i ≠ α ∧ t.1 j ≠ α ∧ i ≠ j)
    (l : Fin k) : sgn α (flipW α i j t) l = if l = i ∨ l = j then -sgn α t l else sgn α t l := by
  split_ifs with hl
  · have hl' : t.1 l ≠ α := by rcases hl with rfl | rfl; exacts [h.1, h.2.1]
    apply sgn_flip (fun e => hl' (Subtype.ext e))
    rw [flipW_val h]; unfold flipFun; rw [if_pos hl, swapc_val hl']
  · unfold sgn; rw [flipW_val h]; unfold flipFun; rw [if_neg hl]

/-- **Orthogonality.** If `D ⊆ S` contains `i` but misses some `j ∈ S`, the character `chi D`
sums to zero over the words of active set `S`. -/
theorem sum_fS_eq_zero {S D : Finset (Fin k)} (hD : D ⊆ S) {i j : Fin k} (hi : i ∈ D)
    (hj : j ∈ S) (hjD : j ∉ D) : ∑ t, fS α S D t = 0 := by
  have hneg : ∀ t, fS α S D (flipW α i j t) = -fS α S D t := by
    intro t
    unfold fS
    rw [sector_flipW]
    by_cases hs : sector α t = S
    · rw [if_pos hs, if_pos hs]
      have hc : t.1 i ≠ α ∧ t.1 j ≠ α ∧ i ≠ j :=
        ⟨mem_sector.mp (hs ▸ hD hi), mem_sector.mp (hs ▸ hj), fun e => hjD (e ▸ hi)⟩
      unfold chi
      rw [← mul_prod_erase D _ hi, ← mul_prod_erase D _ hi, sgn_flipW hc, if_pos (Or.inl rfl)]
      have : ∏ x ∈ D.erase i, sgn α (flipW α i j t) x = ∏ x ∈ D.erase i, sgn α t x := by
        apply prod_congr rfl
        intro l hl
        rw [sgn_flipW hc, if_neg]
        rintro (rfl | rfl)
        · exact (mem_erase.mp hl).1 rfl
        · exact hjD (mem_erase.mp hl).2
      rw [this]; ring
    · rw [if_neg hs, if_neg hs, neg_zero]
  have hinv : Function.Involutive (flipW α i j : TaitWord k → TaitWord k) := flipW_flipW i j
  have h1 := Equiv.sum_comp (hinv.toPerm _) (fun t => fS α S D t)
  simp only [Function.Involutive.coe_toPerm, hneg, sum_neg_distrib] at h1
  linarith

end Flip

section Basis

variable {α : TaitColor}

open Classical in
/-- Index set of the Fourier basis of `kempeSpan k α`: realizable `S`, balanced `U ⊆ S`,
with the normalization `min S ∉ U`. -/
noncomputable def idx (k : ℕ) (α : TaitColor) : Finset (Finset (Fin k) × Finset (Fin k)) :=
  univ.filter (fun p => (∃ t : TaitWord k, sector α t = p.1) ∧ p.2 ⊆ p.1 ∧ Balanced p.1 p.2 ∧
    ∀ h : p.1.Nonempty, p.1.min' h ∉ p.2)

theorem mem_idx {p : Finset (Fin k) × Finset (Fin k)} :
    p ∈ idx k α ↔ (∃ t : TaitWord k, sector α t = p.1) ∧ p.2 ⊆ p.1 ∧ Balanced p.1 p.2 ∧
      ∀ h : p.1.Nonempty, p.1.min' h ∉ p.2 := by
  classical
  unfold idx
  exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨mem_univ _, h⟩⟩

/-- The Fourier basis family. -/
def fam (k : ℕ) (α : TaitColor) (p : idx k α) : TaitWord k → K := fS α p.1.1 p.1.2

theorem fS_mul_fS (S U S' U' : Finset (Fin k)) (t : TaitWord k) :
    fS α S U t * fS α S' U' t = if S = S' then fS α S (symmDiff U U') t else 0 := by
  unfold fS
  by_cases h1 : sector α t = S
  · by_cases h2 : S = S'
    · subst h2; rw [if_pos h1, if_pos h1, if_pos rfl, if_pos h1, chi_mul]
    · rw [if_neg h2, if_pos h1, if_neg (fun h => h2 (h1.symm.trans h)), mul_zero]
  · rw [if_neg h1, zero_mul]
    split_ifs <;> rfl

theorem sum_fS_mul_fS {p q : Finset (Fin k) × Finset (Fin k)} (hp : p ∈ idx k α)
    (hq : q ∈ idx k α) :
    ∑ t, fS α p.1 p.2 t * fS α q.1 q.2 t =
      if p = q then (#(univ.filter (fun t : TaitWord k => sector α t = p.1)) : K) else 0 := by
  rw [mem_idx] at hp hq
  simp_rw [fS_mul_fS]
  by_cases hpq : p = q
  · subst hpq
    simp only [if_true, symmDiff_self]
    unfold fS chi
    simp only [bot_eq_empty, prod_empty]
    rw [sum_boole]
  · rw [if_neg hpq]
    by_cases hS : p.1 = q.1
    · simp only [hS, if_true]
      have hU : p.2 ≠ q.2 := fun h => hpq (Prod.ext hS h)
      obtain ⟨i, hi⟩ := Finset.symmDiff_nonempty.mpr hU
      have hD : symmDiff p.2 q.2 ⊆ q.1 := by
        intro x hx
        rw [mem_symmDiff] at hx
        rcases hx with hx | hx
        · exact hS ▸ hp.2.1 hx.1
        · exact hq.2.1 hx.1
      have hne : q.1.Nonempty := ⟨i, hD hi⟩
      apply sum_fS_eq_zero hD hi (q.1.min'_mem hne)
      rw [mem_symmDiff]
      have h1 := hq.2.2.2 hne
      have h2 := hp.2.2.2 (hS ▸ hne)
      simp only [hS] at h2
      tauto
    · simp [hS]

theorem linearIndependent_fam : LinearIndependent K (fam k α) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg p0
  have h := congrArg (fun F => ∑ t, fS α p0.1.1 p0.1.2 t * F t) hg
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
    sum_const_zero] at h
  simp_rw [mul_sum] at h
  rw [sum_comm] at h
  have hterm : ∀ p : idx k α, ∑ t, fS α p0.1.1 p0.1.2 t * (g p * fam k α p t) =
      if p = p0 then g p0 * (#(univ.filter (fun t : TaitWord k => sector α t = p0.1.1)) : K)
      else 0 := by
    intro p
    have : ∑ t, fS α p0.1.1 p0.1.2 t * (g p * fam k α p t) =
        g p * ∑ t, fS α p.1.1 p.1.2 t * fS α p0.1.1 p0.1.2 t := by
      rw [mul_sum]; apply sum_congr rfl; intro t _; unfold fam; ring
    rw [this, sum_fS_mul_fS p.2 p0.2]
    by_cases hp : p = p0
    · subst hp; simp
    · rw [if_neg (fun h => hp (Subtype.ext h)), if_neg hp, mul_zero]
  rw [sum_congr rfl (fun p _ => hterm p), sum_ite_eq'] at h
  simp only [mem_univ, if_true] at h
  obtain ⟨t0, ht0⟩ := (mem_idx.mp p0.2).1
  have hN : (#(univ.filter (fun t : TaitWord k => sector α t = p0.1.1)) : K) ≠ 0 := by
    have : 0 < #(univ.filter (fun t : TaitWord k => sector α t = p0.1.1)) :=
      card_pos.mpr ⟨t0, mem_filter.mpr ⟨mem_univ _, ht0⟩⟩
    exact_mod_cast this.ne'
  exact (mul_eq_zero.mp h).resolve_right hN

/-- Sum of `(-1)^r` over `Fin n`. -/
theorem sum_neg_one_pow_fin (n : ℕ) :
    ∑ r : Fin n, (-1 : ℤ) ^ (r : ℕ) = if Even n then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun r => (-1 : ℤ) ^ r)]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    by_cases h : Even n
    · rw [if_pos h, if_neg (Nat.not_even_iff_odd.mpr (Even.add_one h)), h.neg_one_pow]; ring
    · have ho := Nat.not_even_iff_odd.mp h
      rw [if_neg h, if_pos ho.add_one, ho.neg_one_pow]; ring

theorem balanced_self {S : Finset (Fin k)} (h : Even #S) : Balanced S S := by
  unfold Balanced
  rw [sum_enum S]
  simp_rw [rank_enum]
  rw [sum_neg_one_pow_fin, if_pos h]

theorem balanced_sdiff {S U : Finset (Fin k)} (hU : U ⊆ S) (h : Even #S) (hb : Balanced S U) :
    Balanced S (S \ U) := by
  have h1 := balanced_self h
  unfold Balanced at *
  rw [sum_sdiff_eq_sub hU, h1, hb, sub_zero]

theorem fS_eq_sign_fS_sdiff {S U : Finset (Fin k)} (hU : U ⊆ S) :
    fS α S U = ((-1 : K) ^ #Sᶜ) • fS α S (S \ U) := by
  funext t
  simp only [Pi.smul_apply, smul_eq_mul]
  unfold fS
  by_cases hs : sector α t = S
  · rw [if_pos hs, if_pos hs]
    have h1 : symmDiff U (S \ U) = S := by
      ext x; rw [mem_symmDiff, mem_sdiff]
      constructor
      · rintro (⟨h, _⟩ | ⟨⟨h, _⟩, _⟩)
        · exact hU h
        · exact h
      · intro hx; by_cases hxU : x ∈ U
        · exact Or.inl ⟨hxU, fun h => h.2 hxU⟩
        · exact Or.inr ⟨⟨hx, hxU⟩, hxU⟩
    have h2 := chi_mul (α := α) U (S \ U) t
    rw [h1, ← hs, chi_sector, hs] at h2
    rw [← h2, mul_assoc, chi_sq, mul_one]
  · rw [if_neg hs, if_neg hs, mul_zero]

theorem fourierSet_subset_span_fam :
    fourierSet k α ⊆ Submodule.span K (Set.range (fam k α)) := by
  rintro f ⟨S, U, ⟨t0, ht0⟩, hUS, hbal, rfl⟩
  by_cases hrep : ∀ h : S.Nonempty, S.min' h ∉ U
  · apply Submodule.subset_span
    exact ⟨⟨(S, U), mem_idx.mpr ⟨⟨t0, ht0⟩, hUS, hbal, hrep⟩⟩, rfl⟩
  · push_neg at hrep
    obtain ⟨hne, hmin⟩ := hrep
    have hev : Even #S := ht0 ▸ even_card_sector t0
    rw [fS_eq_sign_fS_sdiff hUS]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨⟨(S, S \ U), mem_idx.mpr ⟨⟨t0, ht0⟩, sdiff_subset, balanced_sdiff hUS hev hbal, ?_⟩⟩,
      rfl⟩
    intro h hm
    exact (mem_sdiff.mp hm).2 hmin

theorem span_fam_eq : Submodule.span K (Set.range (fam k α)) = kempeSpan k α := by
  rw [kempeSpan_eq_fourier]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro f ⟨p, rfl⟩
    apply Submodule.subset_span
    obtain ⟨h1, h2, h3, _⟩ := mem_idx.mp p.2
    exact ⟨p.1.1, p.1.2, h1, h2, h3, rfl⟩
  · rw [Submodule.span_le]
    exact fourierSet_subset_span_fam

/-- `dim kempeSpan k α = #idx k α`. -/
theorem finrank_kempeSpan (k : ℕ) (α : TaitColor) :
    Module.finrank K (kempeSpan k α) = #(idx k α) := by
  rw [← span_fam_eq, finrank_span_eq_card linearIndependent_fam, Fintype.card_coe]

end Basis

end Theorem62

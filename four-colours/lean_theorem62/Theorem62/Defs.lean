import Mathlib

/-!
# Theorem 62 — public definitions

Everything that appears in the statements of the main theorems is defined here, literally.

* `TaitColor`  : the three nonzero elements of 𝔽₂² = `Fin 2 × Fin 2` (addition = XOR).
* `TaitWord k` : words `t : Fin k → TaitColor` whose XOR-sum is `0`.
* `ringColor`  : prefix XOR-sums, a proper 4-colouring of the cycle `C_k`.
* `NCMatching` : noncrossing perfect matchings of an active set `S ⊆ Fin k`.
* `kempeBlock`, `kempeSpan` : the literal Kempe-block span for a colour `α`.
* `NoncrossingPartition`, `NoAdjBlock`, `blIndicator`, `blSpan` : the BL span.
* `centralTrinomial`, `riordan` : the two integer sequences.
-/

namespace Theorem62

open Finset

/-- The scalar field. -/
abbrev K : Type := ℚ

/-- The Klein four-group 𝔽₂² = `Fin 2 × Fin 2`; `+` is coordinatewise XOR. -/
abbrev F22 : Type := Fin 2 × Fin 2

/-- Tait colours: the three nonzero elements of 𝔽₂². -/
abbrev TaitColor : Type := {c : F22 // c ≠ (0, 0)}

/-- Tait words of length `k`: words in the Tait colours with XOR-sum zero. -/
abbrev TaitWord (k : ℕ) : Type := {t : Fin k → TaitColor // ∑ i, (t i).1 = 0}

/-- The ring colouring of a Tait word: `c i = t 0 ⊕ t 1 ⊕ ⋯ ⊕ t (i-1)` (so `c 0 = (0,0)` and
`c (i+1) = c i ⊕ t i`). -/
def ringColor {k : ℕ} (t : TaitWord k) (i : Fin k) : F22 :=
  ∑ j ∈ univ.filter (fun j : Fin k => j < i), (t.1 j).1

/-! ### Kempe blocks -/

/-- A noncrossing perfect matching of the active set `S`, given by its partner involution
(the values of `partner` outside `S` are irrelevant). Noncrossing: no `a < c < b < d` with
`b = partner a`, `d = partner c`. -/
structure NCMatching (k : ℕ) (S : Finset (Fin k)) where
  partner : Fin k → Fin k
  mem : ∀ i ∈ S, partner i ∈ S
  ne : ∀ i ∈ S, partner i ≠ i
  invol : ∀ i ∈ S, partner (partner i) = i
  noncross : ∀ a ∈ S, ∀ c ∈ S, ¬ (a < c ∧ c < partner a ∧ partner a < partner c)

/-- The active set of `t` for the colour `α`: the positions not coloured `α`. -/
def sector {k : ℕ} (α : TaitColor) (t : TaitWord k) : Finset (Fin k) :=
  univ.filter (fun i => t.1 i ≠ α)

/-- The Kempe block of `t` for colour `α` and matching `M`: all Tait words obtained from `t`
by swapping the two non-`α` colours on an arbitrary union `A` of pairs of `M`.
(On a non-`α` colour `x`, the swap is `x ↦ x ⊕ α`.) -/
def kempeBlock {k : ℕ} (α : TaitColor) (t : TaitWord k) {S : Finset (Fin k)}
    (M : NCMatching k S) : Set (TaitWord k) :=
  {t' | ∃ A ⊆ S, (∀ i ∈ A, M.partner i ∈ A) ∧
      ∀ i, (t'.1 i).1 = if i ∈ A then (t.1 i).1 + α.1 else (t.1 i).1}

/-- The literal Kempe span for colour `α`: the span of the indicators of all Kempe blocks
`kempeBlock α t M`, `t` a Tait word and `M` a noncrossing matching of its active set. -/
def kempeSpan (k : ℕ) (α : TaitColor) : Submodule K (TaitWord k → K) :=
  Submodule.span K
    {f | ∃ (t : TaitWord k) (M : NCMatching k (sector α t)),
      f = (kempeBlock α t M).indicator (fun _ => (1 : K))}

/-! ### The BL span -/

/-- A noncrossing partition of `Fin k`, as an equivalence relation: there are no
`a < c < b < d` with `a ~ b`, `c ~ d` and `¬ a ~ c`. -/
structure NoncrossingPartition (k : ℕ) where
  rel : Fin k → Fin k → Prop
  equiv : Equivalence rel
  noncrossing : ∀ a b c d : Fin k, a < c → c < b → b < d → rel a b → rel c d → rel a c

/-- No block contains two cyclically adjacent positions `i`, `i + 1 mod k`. -/
def NoAdjBlock {k : ℕ} (σ : NoncrossingPartition k) : Prop :=
  ∀ i : Fin k, ¬ σ.rel i (finRotate k i)

/-- Noncrossing partitions without adjacent blocks. -/
abbrev BLPartition (k : ℕ) : Type := {σ : NoncrossingPartition k // NoAdjBlock σ}

/-- `blIndicator k σ t = 1` iff the ring colouring of `t` is constant on every block of `σ`. -/
noncomputable def blIndicator (k : ℕ) (σ : BLPartition k) (t : TaitWord k) : K :=
  open Classical in
  if ∀ i j, σ.1.rel i j → ringColor t i = ringColor t j then 1 else 0

/-- The BL span. -/
noncomputable def blSpan (k : ℕ) : Submodule K (TaitWord k → K) :=
  Submodule.span K (Set.range (blIndicator k))

/-! ### Sequences -/

/-- Central trinomial coefficients `T_k = ∑_m C(k,2m) C(2m,m)`. -/
def centralTrinomial (k : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (k / 2 + 1), Nat.choose k (2 * m) * Nat.choose (2 * m) m

/-- Riordan numbers, by the standard recurrence `R 0 = 1`, `R 1 = 0`,
`(n+1) R n = (n-1) (2 R (n-1) + 3 R (n-2))`; the division is exact (see `riordan_rec`). -/
def riordan : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1) * (2 * riordan (n + 1) + 3 * riordan n) / (n + 3)

/-! ### Basic sanity facts about the definitions -/

theorem ringColor_zero {k : ℕ} (t : TaitWord k) (h : 0 < k) : ringColor t ⟨0, h⟩ = (0, 0) := by
  unfold ringColor
  rw [Finset.sum_eq_zero]
  · rfl
  · intro j hj
    simp only [Finset.mem_filter] at hj
    exact absurd (Fin.lt_def.mp hj.2) (Nat.not_lt_zero _)

end Theorem62

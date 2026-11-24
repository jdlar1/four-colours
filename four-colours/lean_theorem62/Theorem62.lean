import Theorem62.Defs
import Theorem62.Basic
import Theorem62.Matching
import Theorem62.Fourier
import Theorem62.Count
import Theorem62.BLInclusion

/-!
# Theorem 62 — main statements
-/

namespace Theorem62

open Finset

/-- **Theorem B.** `2 · dim 𝔅_α(k) = T_k + (-1)^k`. -/
theorem theorem_B (k : ℕ) (hk : 2 ≤ k) (α : TaitColor) :
    2 * (Module.finrank K (kempeSpan k α) : ℤ) = (centralTrinomial k : ℤ) + (-1 : ℤ) ^ k := by
  rw [finrank_kempeSpan]
  exact two_mul_card_idx α

/-- **Theorem A, inclusion `BL_k ⊆ 𝔅_α ⊓ 𝔅_β`** (any two colours). -/
theorem theorem_A_BL_le (k : ℕ) (α β : TaitColor) :
    blSpan k ≤ kempeSpan k α ⊓ kempeSpan k β :=
  blSpan_le_inf k α β

end Theorem62

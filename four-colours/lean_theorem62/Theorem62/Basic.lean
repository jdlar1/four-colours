import Theorem62.Defs

/-!
# Basic facts: ring colourings are proper, sign characters on 𝔽₂².
-/

namespace Theorem62

open Finset

theorem F22_add_self (x : F22) : x + x = 0 := by
  revert x; decide

theorem F22_eq_of_add_eq_zero {x y : F22} (h : x + y = 0) : x = y := by
  have := congrArg (· + y) h
  simpa [add_assoc, F22_add_self] using this

theorem ringColor_step {k : ℕ} (t : TaitWord k) (i j : Fin k) (h : j.val = i.val + 1) :
    ringColor t j = ringColor t i + (t.1 i).1 := by
  unfold ringColor
  have hset : univ.filter (fun l : Fin k => l < j) =
      insert i (univ.filter (fun l : Fin k => l < i)) := by
    ext l
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.lt_def, Fin.ext_iff]
    omega
  rw [hset, sum_insert (by simp), add_comm]

/-- The ring colouring is a proper 4-colouring of the cycle `C_k`. -/
theorem ringColor_proper {k : ℕ} (t : TaitWord k) (i : Fin k) :
    ringColor t i ≠ ringColor t (finRotate k i) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := i.pos; omega⟩
  by_cases hi : i = Fin.last n
  · subst hi
    have h0 : finRotate (n + 1) (Fin.last n) = ⟨0, by omega⟩ := by
      ext; simp
    rw [h0, ringColor_zero t (by omega)]
    intro hc
    have hsum := t.2
    rw [Fin.sum_univ_castSucc] at hsum
    have hpre : ringColor t (Fin.last n) = ∑ j : Fin n, (t.1 (Fin.castSucc j)).1 := by
      unfold ringColor
      rw [Finset.sum_filter, Fin.sum_univ_castSucc]
      simp [Fin.castSucc_lt_last]
    rw [← hpre] at hsum
    have := F22_eq_of_add_eq_zero hsum
    exact (t.1 (Fin.last n)).2 (this ▸ hc)
  · have hv : (finRotate (n + 1) i).val = i.val + 1 := by
      rw [coe_finRotate, if_neg hi]
    rw [ringColor_step t i _ hv]
    intro hc
    have : (t.1 i).1 = 0 := by
      have h2 := congrArg (ringColor t i + ·) hc
      simp only [← add_assoc, F22_add_self, zero_add] at h2
      exact h2.symm
    exact (t.1 i).2 this

end Theorem62

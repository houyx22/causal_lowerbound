import CausalLowerbound.PartC.AssignmentDyadic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Choose a dyadic transition width within a factor of two of a requested
width. Choosing the slightly wider interval also improves the inverse
power estimate needed for the assignment multiplier. -/
noncomputable section
set_option autoImplicit false
namespace CausalLowerbound.PartC

theorem exists_dyadic_width (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1 / 4) :
    ∃ N : ℕ, 0 < N ∧ w ≤ dyadicWidth N ∧ dyadicWidth N < 2 * w ∧ dyadicWidth N ≤ 1 / 2 := by
  obtain ⟨N, hnext, hprev⟩ := exists_nat_pow_near_of_lt_one hw (show w ≤ 1 by linarith)
    (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hlow : w ≤ dyadicWidth N := hprev
  have hnext' : dyadicWidth (N + 1) < w := hnext
  have hu : dyadicWidth N < 2 * w := by linarith [dyadicWidth_succ N]
  have hn : 0 < N := by
    by_contra h
    have hz : N = 0 := by omega
    simp only [hz, dyadicWidth_zero] at hu
    linarith
  exact ⟨N, hn, hlow, hu, by linarith⟩

theorem dyadicWidth_rpow_le (N : ℕ) (w η : ℝ) (hw : 0 < w) (hη : 0 ≤ η)
    (hwidth : w ≤ dyadicWidth N) : (dyadicWidth N) ^ (-η) ≤ w ^ (-η) :=
  Real.rpow_le_rpow_of_nonpos hw hwidth (neg_nonpos.mpr hη)

end CausalLowerbound.PartC

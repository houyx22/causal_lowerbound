import CausalLowerbound.PartC.AssignmentDyadic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-! Any fixed polynomial in the dyadic depth is bounded by an arbitrarily
small negative power of the actual width. The bound holds at every depth. -/
noncomputable section
set_option autoImplicit false
namespace CausalLowerbound.PartC

theorem dyadic_polynomial_le_rpow (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ C ≥ 0, ∀ N : ℕ, (N + 1 : ℝ) ^ k ≤ C * (dyadicWidth N) ^ (-η) := by
  let r : ℝ := ((2 : ℝ)⁻¹) ^ η
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hη
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ k * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k (by simpa [Real.norm_eq_abs, abs_of_pos hr] using hr1)
  let S := ∑' n : ℕ, (n : ℝ) ^ k * r ^ n
  have hS : 0 ≤ S := tsum_nonneg (fun n => by positivity)
  refine ⟨S / r, div_nonneg hS hr.le, fun N => ?_⟩
  have hN : (N + 1 : ℝ) ^ k * r ^ (N + 1) ≤ S := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hs.le_tsum (N + 1) (fun n hn => by positivity)
  have he : (dyadicWidth N) ^ η = r ^ N :=
    (Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) η N).symm
  rw [Real.rpow_neg (dyadicWidth_pos N).le, he, ← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hr N)).mpr
  apply (le_div_iff₀ hr).mpr
  simpa only [pow_succ, mul_assoc] using hN

end CausalLowerbound.PartC

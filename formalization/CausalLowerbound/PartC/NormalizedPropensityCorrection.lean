import CausalLowerbound.WienerTensor

/-! The surplus multiplier in the normalized degree-one substitution.
No division by the assignment function occurs; the only denominator is
the strictly positive uniform degree weight. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC

open Wiener
variable {d V : Type*} [Fintype d] [Fintype V] [DecidableEq V]

def normalizedPropensityCorrection (M K : Fourier d) (N : ℝ) (i : V) : Fourier (V × d) :=
  liftSlot i (((N⁻¹ : ℝ) • M) ^ 2 * K)

theorem normalizedPropensityCorrection_bound (M K : Fourier d) (N : ℝ)
    (hN : 0 < N) (hM : ‖M‖ ≤ N) (hK : ‖K‖ ≤ 1) (i : V) :
    ‖normalizedPropensityCorrection M K N i‖ ≤ 1 := by
  have hnorm : ‖(N⁻¹ : ℝ) • M‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN)]
    exact (mul_le_mul_of_nonneg_left hM (inv_nonneg.mpr hN.le)).trans_eq (inv_mul_cancel₀ hN.ne')
  apply (liftSlot_norm _ _).trans
  apply (norm_mul_le _ _).trans
  calc
    ‖((N⁻¹ : ℝ) • M) ^ 2‖ * ‖K‖ ≤ 1 * 1 :=
      mul_le_mul ((norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) hnorm)) hK
        (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul _

theorem normalizedPropensityCorrection_value (M K : Fourier d) (N : ℝ) (i : V)
    (x : Torus (V × d)) (m κ : ℝ)
    (hM : toContinuous M (fun j => x (i, j)) = (m : ℂ))
    (hK : toContinuous K (fun j => x (i, j)) = (κ : ℂ)) :
    toContinuous (normalizedPropensityCorrection M K N i) x = ((m / N) ^ 2 * κ : ℝ) := by
  simp only [normalizedPropensityCorrection, liftSlot_value, pow_two, toContinuous_mul,
    ContinuousMap.mul_apply, toContinuous_real_smul, ContinuousMap.smul_apply,
    hM, hK, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div]
  push_cast
  ring

end CausalLowerbound.PartC

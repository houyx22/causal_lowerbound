import CausalLowerbound.WienerDerivativeDecay
import CausalLowerbound.PeriodizedTorus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The Jacobian and Fourier phase for independently rescaled coordinates. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory UnitAddTorus
open scoped BigOperators FourierTransform

namespace CausalLowerbound.Wiener

variable {α : Type*} [Fintype α]

def coordinateScale (N : α → ℕ) (x : α → ℝ) : α → ℝ := fun i => (N i : ℝ) * x i

def scaleHomeomorph (N : α → ℕ) (hN : ∀ i, N i ≠ 0) : (α → ℝ) ≃ₜ (α → ℝ) where
  toFun := coordinateScale N
  invFun := fun x i => x i / N i
  left_inv := by intro x; funext i; simp [coordinateScale, hN]
  right_inv := by
    intro x
    funext i
    have hi : (N i : ℝ) ≠ 0 := by exact_mod_cast hN i
    dsimp [coordinateScale]
    field_simp
  continuous_toFun := continuous_pi (fun i => continuous_const.mul (continuous_apply i))
  continuous_invFun := continuous_pi (fun i => (continuous_apply i).div_const _)

theorem map_coordinateScale (N : α → ℕ) (hN : ∀ i, N i ≠ 0) :
    Measure.map (coordinateScale N) volume = (ENNReal.ofReal (∏ i, (N i : ℝ)⁻¹)) • volume := by
  classical
  have hdet : Matrix.det (Matrix.diagonal (fun i => (N i : ℝ))) ≠ 0 := by
    simp only [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast hN i)
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  have hpos : 0 ≤ (∏ i, (N i : ℝ))⁻¹ := by positivity
  simpa only [Matrix.diagonal_toLin', LinearMap.pi_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, coordinateScale, Matrix.det_diagonal,
    abs_of_nonneg hpos, Finset.prod_inv_distrib] using h

theorem integral_coordinateScale (g : (α → ℝ) → ℂ) (N : α → ℕ) (hN : ∀ i, N i ≠ 0) :
    (∫ x, g (coordinateScale N x)) = (∏ i, (N i : ℝ)⁻¹) • ∫ x, g x := by
  have hm := (scaleHomeomorph N hN).toMeasurableEquiv.measurableEmbedding.integral_map
    (μ := (volume : Measure (α → ℝ))) g
  change (∫ y, g y ∂Measure.map (coordinateScale N) volume) =
    (∫ x, g (coordinateScale N x)) at hm
  rw [map_coordinateScale N hN, integral_smul_measure,
    ENNReal.toReal_ofReal (Finset.prod_nonneg (fun _ _ => by positivity))] at hm
  exact hm.symm

def fourierPhase (w x : α → ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * ∑ i, x i * w i : ℝ) : ℂ) * Complex.I)

theorem mFourier_projection_phase (k : α → ℤ) (x : α → ℝ) :
    mFourier (-k) (torusProjection x) = fourierPhase (fun i => (k i : ℝ)) x := by
  simp only [mFourier, ContinuousMap.coe_mk, torusProjection, fourier_coe_apply,
    Pi.neg_apply, Int.cast_neg, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  unfold fourierPhase
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
    Complex.ofReal_sum, Complex.ofReal_intCast, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fourierPhase_scaled (N : α → ℕ) (hN : ∀ i, N i ≠ 0) (k : α → ℤ) (x : α → ℝ) :
    fourierPhase (fun i => (k i : ℝ) / N i) (coordinateScale N x) =
      fourierPhase (fun i => (k i : ℝ)) x := by
  have hs : (∑ i, coordinateScale N x i * ((k i : ℝ) / N i)) =
      ∑ i, x i * (k i : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [coordinateScale]
    have hi : (N i : ℝ) ≠ 0 := by exact_mod_cast hN i
    field_simp
    ring
  simp only [fourierPhase, hs]

theorem fourierIntegral_pi (f : (α → ℝ) → ℂ) (w : EuclideanSpace ℝ α) :
    𝓕 (fun y : EuclideanSpace ℝ α => f (fun i => y i)) w =
      ∫ x : α → ℝ, fourierPhase (fun i => w i) x * f x := by
  rw [Real.fourierIntegral_eq']
  have hv := EuclideanSpace.volume_preserving_measurableEquiv α
  rw [← (MeasurePreserving.symm (EuclideanSpace.measurableEquiv α) hv).integral_comp']
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [EuclideanSpace.measurableEquiv, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
    WithLp.equiv_symm_pi_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    smul_eq_mul, fourierPhase]
  simp only [mul_comm]

end CausalLowerbound.Wiener

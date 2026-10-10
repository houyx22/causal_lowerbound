import CausalLowerbound.UpperBound.TwoScaleContrast
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix

/-! Construct normalized cancellation weights by solving a square
interpolation system. `none` is the close partner; `some i` are the coarse
unisolvent nodes (one of which is the anchor). -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix

namespace CausalLowerbound.UpperBound

variable {I : Type*} [Fintype I] [DecidableEq I]

def interpolationCoefficients (A : Matrix I I ℝ) (b : I → ℝ) : I → ℝ := A⁻¹ *ᵥ b

theorem interpolationCoefficients_solve (A : Matrix I I ℝ) (b : I → ℝ)
    (hA : IsUnit A.det) : A *ᵥ interpolationCoefficients A b = b := by
  rw [interpolationCoefficients, Matrix.mulVec_mulVec, A.mul_nonsing_inv hA,
    Matrix.one_mulVec]

theorem interpolationCoefficients_column (A : Matrix I I ℝ) (hA : IsUnit A.det)
    (j : I) : interpolationCoefficients A (fun i => A i j) = Pi.single j 1 := by
  have he : (fun i => A i j) = A *ᵥ Pi.single j 1 := by
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [he, interpolationCoefficients, Matrix.mulVec_mulVec, A.nonsing_inv_mul hA,
    Matrix.one_mulVec]

theorem interpolationCoefficients_perturbation (A : Matrix I I ℝ) (b b₀ : I → ℝ)
    {C δ : ℝ} (hδ : 0 ≤ δ) (hA : ∀ i, ∑ j, |A⁻¹ i j| ≤ C)
    (hb : ∀ j, |b j - b₀ j| ≤ δ) (i : I) :
    |interpolationCoefficients A b i - interpolationCoefficients A b₀ i| ≤ C * δ := by
  change |∑ j, A⁻¹ i j * b j - ∑ j, A⁻¹ i j * b₀ j| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |A⁻¹ i j * b j - A⁻¹ i j * b₀ j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A⁻¹ i j| * |b j - b₀ j| := by simp_rw [← mul_sub, abs_mul]
    _ ≤ ∑ j, |A⁻¹ i j| * δ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)
    _ = (∑ j, |A⁻¹ i j|) * δ := (Finset.sum_mul _ _ _).symm
    _ ≤ C * δ := mul_le_mul_of_nonneg_right (hA i) hδ

def stencilNormalizer (c : I → ℝ) : ℝ := Real.sqrt (1 + ∑ i, c i ^ 2)

omit [DecidableEq I] in
theorem stencilNormalizer_ge_one (c : I → ℝ) : 1 ≤ stencilNormalizer c := by
  have hs : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have he := Real.sq_sqrt (show 0 ≤ 1 + ∑ i, c i ^ 2 by linarith)
  have hn := Real.sqrt_nonneg (1 + ∑ i, c i ^ 2)
  unfold stencilNormalizer
  nlinarith

omit [DecidableEq I] in
theorem stencilNormalizer_pos (c : I → ℝ) : 0 < stencilNormalizer c :=
  lt_of_lt_of_le zero_lt_one (stencilNormalizer_ge_one c)

def normalizedStencil (c : I → ℝ) : Option I → ℝ
  | none => -1 / stencilNormalizer c
  | some i => c i / stencilNormalizer c

omit [DecidableEq I] in
theorem normalizedStencil_norm_sq (c : I → ℝ) : ∑ i, normalizedStencil c i ^ 2 = 1 := by
  have hd := stencilNormalizer_pos c
  have he : stencilNormalizer c ^ 2 = 1 + ∑ i, c i ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [Fintype.sum_option]
  simp only [normalizedStencil, div_pow, neg_one_sq, one_div]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  field_simp
  nlinarith [he]

omit [DecidableEq I] in
theorem normalizedStencil_partner_bound (c : I → ℝ) : |normalizedStencil c none| ≤ 1 := by
  rw [normalizedStencil, abs_div, abs_neg, abs_one,
    abs_of_pos (stencilNormalizer_pos c)]
  exact (div_le_one (stencilNormalizer_pos c)).mpr (stencilNormalizer_ge_one c)

omit [DecidableEq I] in
theorem normalizedStencil_coefficient_bound (c : I → ℝ) (i : I) :
    |normalizedStencil c (some i)| ≤ |c i| := by
  rw [normalizedStencil, abs_div, abs_of_pos (stencilNormalizer_pos c)]
  exact div_le_self (abs_nonneg _) (stencilNormalizer_ge_one c)

omit [DecidableEq I] in
theorem normalizedStencil_cancel (c m : I → ℝ) (partner : ℝ)
    (hm : ∑ i, c i * m i = partner) :
    normalizedStencil c none * partner + ∑ i, normalizedStencil c (some i) * m i = 0 := by
  simp only [normalizedStencil]
  simp_rw [div_mul_eq_mul_div]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, hm]
  ring

/-- Every row of the evaluation matrix is annihilated by the constructed weights. -/
theorem interpolatedStencil_cancel (A : Matrix I I ℝ) (b : I → ℝ)
    (hA : IsUnit A.det) (j : I) :
    normalizedStencil (interpolationCoefficients A b) none * b j +
      ∑ i, normalizedStencil (interpolationCoefficients A b) (some i) * A j i = 0 := by
  apply normalizedStencil_cancel
  have he := congrFun (interpolationCoefficients_solve A b hA) j
  simpa only [Matrix.mulVec, dotProduct, mul_comm] using he

/-- Bounded inverse rows and a nearby partner column give the required
small auxiliary weights, directly from the chosen inverse construction. -/
theorem interpolatedStencil_auxiliary_bound (A : Matrix I I ℝ) (b : I → ℝ)
    (hA : IsUnit A.det) (anchor : I) {C δ : ℝ} (hδ : 0 ≤ δ)
    (hrow : ∀ i, ∑ j, |A⁻¹ i j| ≤ C) (hcol : ∀ j, |b j - A j anchor| ≤ δ)
    (i : I) (hi : i ≠ anchor) :
    |normalizedStencil (interpolationCoefficients A b) (some i)| ≤ C * δ := by
  have hc := interpolationCoefficients_perturbation A b (fun j => A j anchor) hδ hrow hcol i
  rw [interpolationCoefficients_column A hA anchor] at hc
  simp only [Pi.single_eq_of_ne hi, sub_zero] at hc
  exact (normalizedStencil_coefficient_bound _ i).trans hc

theorem interpolatedStencil_anchor_positive (A : Matrix I I ℝ) (b : I → ℝ)
    (hA : IsUnit A.det) (anchor : I) {C δ : ℝ} (hδ : 0 ≤ δ)
    (hrow : ∀ i, ∑ j, |A⁻¹ i j| ≤ C) (hcol : ∀ j, |b j - A j anchor| ≤ δ)
    (hsmall : C * δ < 1) :
    0 < normalizedStencil (interpolationCoefficients A b) (some anchor) := by
  have hc := interpolationCoefficients_perturbation A b (fun j => A j anchor) hδ hrow hcol anchor
  rw [interpolationCoefficients_column A hA anchor] at hc
  simp only [Pi.single_eq_same] at hc
  apply div_pos _ (stencilNormalizer_pos _)
  have hh := (abs_le.mp hc).1
  linarith

omit [DecidableEq I] in
theorem continuous_stencilNormalizer : Continuous (stencilNormalizer (I := I)) := by
  unfold stencilNormalizer
  fun_prop

omit [DecidableEq I] in
theorem continuous_normalizedStencil (i : Option I) :
    Continuous (fun c : I → ℝ => normalizedStencil c i) := by
  cases i with
  | none =>
    exact continuous_const.div (continuous_stencilNormalizer (I := I))
      (fun c => (stencilNormalizer_pos c).ne')
  | some i =>
    exact (continuous_apply i).div (continuous_stencilNormalizer (I := I))
      (fun c => (stencilNormalizer_pos c).ne')

end CausalLowerbound.UpperBound

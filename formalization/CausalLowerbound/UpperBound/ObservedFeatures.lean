import CausalLowerbound.UpperBound.ObservedStencil

/-! Polynomial features and their weighted average on accepted observations.
The normalization has unit squared weight sum on every input, including
singular interpolation configurations outside the acceptance event. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

def stencilFeature (p : ℕ) (x₀ : d → ℝ) (h : ℝ)
    (X : StencilRole d p → d → ℝ) (i : StencilRole d p) (ν : TensorIndex d p) : ℝ :=
  tensorMonomial p ν (normalizedDisplacement x₀ x₀ (X i) h)

def stencilFeatureMean (p : ℕ) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (X : StencilRole d p → d → ℝ) (ν : TensorIndex d p) : ℝ :=
  ∑ i, observedStencilWeights p x₀ ℓ r X i ^ 2 * stencilFeature p x₀ h X i ν

theorem observedStencilWeights_norm_sq (p : ℕ) (x₀ : d → ℝ) (ℓ r : ℝ)
    (X : StencilRole d p → d → ℝ) : ∑ i, observedStencilWeights p x₀ ℓ r X i ^ 2 = 1 :=
  completedStencil_norm_sq _

theorem stencilFeature_continuous (p : ℕ) (x₀ : d → ℝ) (h : ℝ)
    (i : StencilRole d p) (ν : TensorIndex d p) :
    Continuous (fun X => stencilFeature p x₀ h X i ν) := by
  unfold stencilFeature normalizedDisplacement inwardReflection
  apply (continuous_tensorMonomial p ν).comp
  fun_prop

theorem stencilFeatureMean_measurable (p : ℕ) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (ν : TensorIndex d p) : Measurable (fun X => stencilFeatureMean p x₀ h ℓ r X ν) := by
  have hw := observedStencilWeights_measurable p x₀ ℓ r
  apply Finset.measurable_sum
  intro i _
  exact (((measurable_pi_apply i).comp hw).pow_const 2).mul
    (stencilFeature_continuous p x₀ h i ν).measurable

theorem tensorMonomial_abs_le_one (p : ℕ) (ν : TensorIndex d p) (u : d → ℝ)
    (hu : ‖u‖ ≤ 1) : |tensorMonomial p ν u| ≤ 1 := by
  rw [tensorMonomial, Finset.abs_prod]
  apply Finset.prod_le_one
  · intro i _
    exact abs_nonneg _
  · intro i _
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (by simpa only [Real.norm_eq_abs] using
      ((norm_le_pi_norm u i).trans hu))

theorem acceptedStencil_displacement_norm_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (X : StencilRole d p → d → ℝ) (hX : X ∈ acceptedStencil p T x₀ h ℓ r)
    (i : StencilRole d p) : ‖normalizedDisplacement x₀ x₀ (X i) h‖ ≤ 1 := by
  have hg := physicalStencil_geometry p T x₀ (observedAnchorCoordinate p x₀ h X)
    (observedAuxiliaryCoordinates p x₀ r X) (observedPartnerCoordinate p x₀ ℓ X)
    hx hh hhsmall hℓ hℓr hrh
    (fun a => ⟨hX.1.1 a, hX.1.2 a⟩)
    (fun a => ⟨hX.2.1.1 a, hX.2.1.2 a⟩) hX.2.2 i
  rw [observedStencil_reconstruct p x₀ h ℓ r hh.ne' hℓ.ne' (hℓ.trans_le hℓr).ne' X] at hg
  rw [normalizedDisplacement, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh,
    inwardReflection_norm]
  calc
    _ ≤ h⁻¹ * h := mul_le_mul_of_nonneg_left hg.2 (inv_nonneg.mpr hh.le)
    _ = 1 := inv_mul_cancel₀ hh.ne'

theorem acceptedStencil_feature_bound (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (X : StencilRole d p → d → ℝ) (hX : X ∈ acceptedStencil p T x₀ h ℓ r)
    (i : StencilRole d p) (ν : TensorIndex d p) : |stencilFeature p x₀ h X i ν| ≤ 1 :=
  tensorMonomial_abs_le_one p ν _
    (acceptedStencil_displacement_norm_le p T x₀ hx hh hhsmall hℓ hℓr hrh X hX i)

theorem stencilFeatureMean_bound (p : ℕ) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (X : StencilRole d p → d → ℝ) (ν : TensorIndex d p)
    (hφ : ∀ i, |stencilFeature p x₀ h X i ν| ≤ 1) : |stencilFeatureMean p x₀ h ℓ r X ν| ≤ 1 := by
  calc
    _ ≤ ∑ i, |observedStencilWeights p x₀ ℓ r X i ^ 2 * stencilFeature p x₀ h X i ν| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, observedStencilWeights p x₀ ℓ r X i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_sq]
      exact mul_le_of_le_one_right (sq_nonneg _) (hφ i)
    _ = 1 := observedStencilWeights_norm_sq p x₀ ℓ r X

end CausalLowerbound.UpperBound

import CausalLowerbound.UpperBound.MatrixComparison
import CausalLowerbound.UpperBound.PopulationBias

/-! The actual population matrix is close to a positive anchor Gram matrix.
The leading weight may depend on every covariate in the tuple.  Propensity
measurability is obtained from the conditional mean, so the model is not
strengthened by a pointwise measurability assumption. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound.RealOutcomeModel

variable {d : Type*} [Fintype d] {ε lower upper M₂ : ℝ}
variable (M : RealOutcomeModel d ε lower upper M₂)

theorem propensity_aestronglyMeasurable : AEStronglyMeasurable M.propensity M.design := by
  have hm : StronglyMeasurable (fun x => ∫ z, treatmentValue z ∂M.conditional x) :=
    measurable_treatmentValue.stronglyMeasurable.integral_kernel
  exact hm.aestronglyMeasurable.congr M.treatment_mean

theorem tuple_propensity_aestronglyMeasurable {I : Type*} [Fintype I] (i : I) :
    AEStronglyMeasurable (fun X : I → d → ℝ => M.propensity (X i))
      (Measure.pi (fun _ : I => M.design)) :=
  M.propensity_aestronglyMeasurable.comp_measurePreserving
    (coordinate_eval_measurePreserving (fun _ : I => M.design) i)

theorem tuple_propensity_overlap {I : Type*} [Fintype I] :
    ∀ᵐ X ∂Measure.pi (fun _ : I => M.design), ∀ i, ε ≤ M.propensity (X i) ∧
      M.propensity (X i) ≤ 1 - ε :=
  ae_all_iff.mpr (fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : I => M.design) (i := i)).eventually M.overlap)

def stencilTreatmentVariance (p : ℕ) (x₀ : d → ℝ) (ℓ r : ℝ)
    (X : StencilRole d p → d → ℝ) : ℝ :=
  weightedTreatmentVariance (observedStencilWeights p x₀ ℓ r X) (fun i => M.propensity (X i))

theorem stencilTreatmentVariance_aestronglyMeasurable (p : ℕ) (x₀ : d → ℝ) (ℓ r : ℝ) :
    AEStronglyMeasurable (M.stencilTreatmentVariance p x₀ ℓ r)
      (Measure.pi (fun _ : StencilRole d p => M.design)) := by
  have hw (i : StencilRole d p) :=
    ((measurable_pi_apply i).comp (observedStencilWeights_measurable p x₀ ℓ r)).aestronglyMeasurable
      (μ := Measure.pi (fun _ : StencilRole d p => M.design))
  exact Finset.aestronglyMeasurable_sum _ (fun i _ =>
    (((hw i).pow 2).mul (M.tuple_propensity_aestronglyMeasurable i)).mul
      (aestronglyMeasurable_const.sub (M.tuple_propensity_aestronglyMeasurable i)))

theorem stencilTreatmentVariance_bounds (p : ℕ) (x₀ : d → ℝ) (ℓ r : ℝ) (hε : 0 ≤ ε) :
    ∀ᵐ X ∂Measure.pi (fun _ : StencilRole d p => M.design),
      0 ≤ M.stencilTreatmentVariance p x₀ ℓ r X ∧
      M.stencilTreatmentVariance p x₀ ℓ r X ≤ 1 ∧
      ε * (1 - ε) ≤ M.stencilTreatmentVariance p x₀ ℓ r X := by
  filter_upwards [M.tuple_propensity_mem_unit (I := StencilRole d p) hε,
    M.tuple_propensity_overlap (I := StencilRole d p)] with X hπ ho
  have hc := weightedTreatmentVariance_mem_unit _ _ (observedStencilWeights_norm_sq p x₀ ℓ r X) hπ
  exact ⟨hc.1, hc.2, weightedTreatmentVariance_lower _ _ (observedStencilWeights_norm_sq p x₀ ℓ r X) ho⟩

def stencilLeadingKernel (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (ν ω : TensorIndex d p) (X : StencilRole d p → d → ℝ) : ℝ :=
  (acceptedStencil p T x₀ h ℓ r).indicator (fun X => M.stencilTreatmentVariance p x₀ ℓ r X *
    stencilFeature p x₀ h X (some none) ν * stencilFeature p x₀ h X (some none) ω) X

def stencilLeadingGram (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ) :
    Matrix (TensorIndex d p) (TensorIndex d p) ℝ :=
  fun ν ω => ∫ X, M.stencilLeadingKernel p T x₀ h ℓ r ν ω X
    ∂Measure.pi (fun _ : StencilRole d p => M.design)

def stencilConditionalMatrixKernel (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (ν ω : TensorIndex d p) (X : StencilRole d p → d → ℝ) : ℝ :=
  (acceptedStencil p T x₀ h ℓ r).indicator (fun X => stencilFeatureMean p x₀ h ℓ r X ν *
    matrixPopulationValue (observedStencilWeights p x₀ ℓ r X)
      (fun i => M.propensity (X i)) (fun i => stencilFeature p x₀ h X i ω)) X

theorem stencilLeadingKernel_aestronglyMeasurable (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (ν ω : TensorIndex d p) :
    AEStronglyMeasurable (M.stencilLeadingKernel p T x₀ h ℓ r ν ω)
      (Measure.pi (fun _ : StencilRole d p => M.design)) :=
  (((M.stencilTreatmentVariance_aestronglyMeasurable p x₀ ℓ r).mul
    (stencilFeature_continuous p x₀ h (some none) ν).measurable.aestronglyMeasurable).mul
    (stencilFeature_continuous p x₀ h (some none) ω).measurable.aestronglyMeasurable).indicator
    (acceptedStencil_measurable p T x₀ h ℓ r)

theorem stencilConditionalMatrixKernel_aestronglyMeasurable (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (ν ω : TensorIndex d p) :
    AEStronglyMeasurable (M.stencilConditionalMatrixKernel p T x₀ h ℓ r ν ω)
      (Measure.pi (fun _ : StencilRole d p => M.design)) := by
  have hw (i : StencilRole d p) :=
    ((measurable_pi_apply i).comp (observedStencilWeights_measurable p x₀ ℓ r)).aestronglyMeasurable
      (μ := Measure.pi (fun _ : StencilRole d p => M.design))
  have hφ (i : StencilRole d p) := (stencilFeature_continuous p x₀ h i ω).measurable.aestronglyMeasurable
    (μ := Measure.pi (fun _ : StencilRole d p => M.design))
  have hs := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
    (hw i).mul (M.tuple_propensity_aestronglyMeasurable i))
  have ht := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
    ((hw i).mul (M.tuple_propensity_aestronglyMeasurable i)).mul (hφ i))
  have hv := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
    ((((hw i).pow 2).mul (M.tuple_propensity_aestronglyMeasurable i)).mul
      ((aestronglyMeasurable_const (b := (1 : ℝ))).sub (M.tuple_propensity_aestronglyMeasurable i))).mul (hφ i))
  exact ((stencilFeatureMean_measurable p x₀ h ℓ r ν).aestronglyMeasurable.mul
    ((hs.mul ht).add hv)).indicator (acceptedStencil_measurable p T x₀ h ℓ r)

theorem stencilLeadingKernel_memLp (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (hε : 0 ≤ ε) (ν ω : TensorIndex d p) :
    MemLp (M.stencilLeadingKernel p T x₀ h ℓ r ν ω) 2
      (Measure.pi (fun _ : StencilRole d p => M.design)) := by
  apply MemLp.of_bound (M.stencilLeadingKernel_aestronglyMeasurable p T x₀ h ℓ r ν ω) 1
  filter_upwards [M.stencilTreatmentVariance_bounds p x₀ ℓ r hε] with X hc
  by_cases hX : X ∈ acceptedStencil p T x₀ h ℓ r
  · rw [stencilLeadingKernel, Set.indicator_of_mem hX, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg hc.1]
    exact mul_le_one₀ (mul_le_one₀ hc.2.1 (abs_nonneg _)
      (acceptedStencil_feature_bound p T x₀ hx hh hhsmall hℓ hℓr hrh X hX _ ν))
      (abs_nonneg _) (acceptedStencil_feature_bound p T x₀ hx hh hhsmall hℓ hℓr hrh X hX _ ω)
  · simp only [stencilLeadingKernel, Set.indicator_of_not_mem hX, norm_zero, zero_le_one]

theorem stencilConditionalMatrixKernel_memLp (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (hε : 0 ≤ ε) (ν ω : TensorIndex d p) :
    MemLp (M.stencilConditionalMatrixKernel p T x₀ h ℓ r ν ω) 2
      (Measure.pi (fun _ : StencilRole d p => M.design)) := by
  apply MemLp.of_bound (M.stencilConditionalMatrixKernel_aestronglyMeasurable p T x₀ h ℓ r ν ω)
    ((Fintype.card (StencilRole d p) : ℝ) ^ 2 + 1)
  filter_upwards [M.tuple_propensity_mem_unit (I := StencilRole d p) hε] with X hπ
  by_cases hX : X ∈ acceptedStencil p T x₀ h ℓ r
  · have hφ (i : StencilRole d p) (a : TensorIndex d p) :=
      acceptedStencil_feature_bound p T x₀ hx hh hhsmall hℓ hℓr hrh X hX i a
    rw [stencilConditionalMatrixKernel, Set.indicator_of_mem hX, Real.norm_eq_abs, abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _)
      (stencilFeatureMean_bound p x₀ h ℓ r X ν (fun i => hφ i ν))).trans
      (matrixPopulationValue_abs_le _ _ _ (observedStencilWeights_norm_sq p x₀ ℓ r X) hπ (fun i => hφ i ω))
  · rw [stencilConditionalMatrixKernel, Set.indicator_of_not_mem hX, norm_zero]
    positivity

theorem stencilPopulationMatrix_perturbation (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r A : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (hε : 0 ≤ ε) (hupper : 0 ≤ upper)
    (hA : 0 ≤ A)
    (hcontrast : ∀ X ∈ acceptedStencil p T x₀ h ℓ r,
      |∑ i, observedStencilWeights p x₀ ℓ r X i * M.propensity (X i)| ≤ A)
    (ν ω : TensorIndex d p) :
    |M.stencilPopulationMatrix p T x₀ h ℓ r ν ω - M.stencilLeadingGram p T x₀ h ℓ r ν ω| ≤
      (A * (A + stencilFeatureVariationBound p T h ℓ) + 2 * stencilFeatureVariationBound p T h ℓ) *
        upper ^ Fintype.card (StencilRole d p) * stencilMass p T h ℓ r := by
  let V := stencilFeatureVariationBound p T h ℓ
  let C := A * (A + V) + 2 * V
  have hV : 0 ≤ V := stencilFeatureVariationBound_nonneg p T hh.le hℓ.le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ᵐ X ∂Measure.pi (fun _ : StencilRole d p => M.design),
      ‖M.stencilConditionalMatrixKernel p T x₀ h ℓ r ν ω X - M.stencilLeadingKernel p T x₀ h ℓ r ν ω X‖ ≤
        (acceptedStencil p T x₀ h ℓ r).indicator (fun _ => C) X := by
    filter_upwards [M.tuple_propensity_mem_unit (I := StencilRole d p) hε] with X hπ
    by_cases hX : X ∈ acceptedStencil p T x₀ h ℓ r
    · simp only [stencilConditionalMatrixKernel, stencilLeadingKernel, Set.indicator_of_mem hX, Real.norm_eq_abs]
      exact matrixPopulationValue_anchor_comparison _ _ _ _ _ _
        (observedStencilWeights_norm_sq p x₀ ℓ r X) hπ
        (fun i => acceptedStencil_feature_bound p T x₀ hx hh hhsmall hℓ hℓr hrh X hX i ν)
        (fun i => acceptedStencil_feature_bound p T x₀ hx hh hhsmall hℓ hℓr hrh X hX i ω)
        (acceptedStencil_feature_bound p T x₀ hx hh hhsmall hℓ hℓr hrh X hX _ ν)
        (acceptedStencil_feature_bound p T x₀ hx hh hhsmall hℓ hℓr hrh X hX _ ω)
        hA hV (hcontrast X hX)
        (acceptedStencil_feature_variation p T x₀ hx hh hhsmall hℓ hℓr hrh X hX ν)
        (acceptedStencil_feature_variation p T x₀ hx hh hhsmall hℓ hℓr hrh X hX ω)
    · simp only [stencilConditionalMatrixKernel, stencilLeadingKernel,
        Set.indicator_of_not_mem hX, sub_self, norm_zero, le_refl]
  have he := norm_integral_le_of_norm_le
    ((integrable_const C).indicator (acceptedStencil_measurable p T x₀ h ℓ r)) hbound
  rw [integral_sub
    ((M.stencilConditionalMatrixKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh hε ν ω).integrable one_le_two)
    ((M.stencilLeadingKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh hε ν ω).integrable one_le_two),
    integral_indicator_const _ (acceptedStencil_measurable p T x₀ h ℓ r)] at he
  rw [M.stencilPopulationMatrix_integral p T x₀ hx hh hhsmall hℓ hℓr hrh ν ω]
  change |(∫ X, M.stencilConditionalMatrixKernel p T x₀ h ℓ r ν ω X ∂Measure.pi (fun _ : StencilRole d p => M.design)) -
    M.stencilLeadingGram p T x₀ h ℓ r ν ω| ≤ _
  apply (show |(∫ X, M.stencilConditionalMatrixKernel p T x₀ h ℓ r ν ω X ∂Measure.pi (fun _ : StencilRole d p => M.design)) -
    M.stencilLeadingGram p T x₀ h ℓ r ν ω| ≤ C * (Measure.pi (fun _ : StencilRole d p => M.design)).real
      (acceptedStencil p T x₀ h ℓ r) by simpa only [Real.norm_eq_abs, smul_eq_mul, mul_comm, stencilLeadingGram] using he).trans
  simpa only [C, V, mul_assoc] using mul_le_mul_of_nonneg_left
    (M.acceptedStencil_probability_real_le_mass p T x₀ hh hℓ (hℓ.trans_le hℓr) hupper) hC

end CausalLowerbound.UpperBound.RealOutcomeModel

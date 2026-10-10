import CausalLowerbound.UpperBound.EmpiricalKernels
import CausalLowerbound.UpperBound.TupleLaw
import CausalLowerbound.UpperBound.OverlapBounds

/-! Acceptance-sensitive second moments for the concrete empirical kernels.
The response kernel is integrated conditionally on the whole covariate tuple,
so its second moment retains the acceptance probability even for unbounded Y. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ProbabilityTheory Classical

namespace CausalLowerbound.UpperBound.RealOutcomeModel

variable {d : Type*} [Fintype d] {ε lower upper M₂ : ℝ}
variable (M : RealOutcomeModel d ε lower upper M₂)

theorem sampleLaw_secondMoment_le_event {I : Type*} [Fintype I]
    {K : (I → (d → ℝ) × (Bool × ℝ)) → ℝ} (hK : MemLp K 2 (M.sampleLaw I))
    (E : Set (I → d → ℝ)) (hE : MeasurableSet E) (C : ℝ)
    (hc : ∀ᵐ X ∂Measure.pi (fun _ : I => M.design),
      (∫ z, K (fun i => (X i, z i)) ^ 2 ∂M.conditionalTupleLaw X) ≤ E.indicator (fun _ => C) X) :
    (∫ z, K z ^ 2 ∂M.sampleLaw I) ≤ C * (Measure.pi (fun _ : I => M.design)).real E := by
  have hmp := M.tupleLaw_measurePreserving (I := I)
  have hi : Integrable
      (fun z : (I → d → ℝ) × (I → Bool × ℝ) => K (fun i => (z.1 i, z.2 i)) ^ 2)
      ((Measure.pi (fun _ : I => M.design)) ⊗ₘ M.conditionalTupleKernel I) :=
    (hmp.integrable_comp hK.integrable_sq.aestronglyMeasurable).mpr hK.integrable_sq
  have hi' := ((Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi).2
  have hint : Integrable
      (fun X => ∫ z, K (fun i => (X i, z i)) ^ 2 ∂M.conditionalTupleLaw X)
      (Measure.pi (fun _ : I => M.design)) := by
    simpa only [Real.norm_eq_abs, abs_sq, conditionalTupleKernel_apply] using hi'
  rw [M.integral_sampleLaw_via_conditional hK.integrable_sq]
  calc
    _ ≤ ∫ X, E.indicator (fun _ => C) X ∂Measure.pi (fun _ : I => M.design) :=
      integral_mono_ae hint ((integrable_const C).indicator hE) hc
    _ = _ := by rw [integral_indicator_const C hE]; simp only [smul_eq_mul, mul_comm]

theorem stencilResponseKernel_secondMoment_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (ν : TensorIndex d p) :
    (∫ z, stencilResponseKernel p T x₀ h ℓ r ν z ^ 2 ∂M.sampleLaw (StencilRole d p)) ≤
      (2 * M₂ * (Fintype.card (StencilRole d p) : ℝ) ^ 2) *
        (Measure.pi (fun _ : StencilRole d p => M.design)).real (acceptedStencil p T x₀ h ℓ r) := by
  apply M.sampleLaw_secondMoment_le_event
    (M.stencilResponseKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh ν)
    (acceptedStencil p T x₀ h ℓ r) (acceptedStencil_measurable p T x₀ h ℓ r)
  filter_upwards [M.conditional_score_secondMoment_le (I := StencilRole d p)] with X hX
  by_cases ha : X ∈ acceptedStencil p T x₀ h ℓ r
  · rw [Set.indicator_of_mem ha]
    have hm := stencilFeatureMean_bound p x₀ h ℓ r X ν
      (fun i => acceptedStencil_feature_bound p T x₀ hx hh hhsmall hℓ hℓr hrh X ha i ν)
    have hm₂ := (sq_le_one_iff_abs_le_one _).mpr hm
    have hb := hX (observedStencilWeights p x₀ ℓ r X) 0 (observedStencilWeights_norm_sq p x₀ ℓ r X)
    have he (z : StencilRole d p → Bool × ℝ) :
        stencilResponseKernel p T x₀ h ℓ r ν (fun i => (X i, z i)) ^ 2 =
          stencilFeatureMean p x₀ h ℓ r X ν ^ 2 *
            residualScore (observedStencilWeights p x₀ ℓ r X) 0 z ^ 2 := by
      simp only [stencilResponseKernel, acceptedObservationStencil, Set.mem_setOf_eq, ha, if_true, mul_pow]
    simp_rw [he]
    rw [integral_const_mul]
    calc
      _ ≤ ∫ z, residualScore (observedStencilWeights p x₀ ℓ r X) 0 z ^ 2
          ∂M.conditionalTupleLaw X :=
        mul_le_of_le_one_left (integral_nonneg (fun z => sq_nonneg _)) hm₂
      _ ≤ (Fintype.card (StencilRole d p) : ℝ) *
          ∑ i : StencilRole d p, (2 * M₂ + 2 * (0 : StencilRole d p → ℝ) i ^ 2) := hb
      _ = _ := by simp only [Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  · rw [Set.indicator_of_not_mem ha]
    have he (z : StencilRole d p → Bool × ℝ) :
        stencilResponseKernel p T x₀ h ℓ r ν (fun i => (X i, z i)) = 0 := by
      exact stencilResponseKernel_off p T x₀ h ℓ r ν _ ha
    simp only [he, zero_pow (by decide : 2 ≠ 0), integral_zero, le_refl]

theorem stencilMatrixKernel_secondMoment_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (ν ω : TensorIndex d p) :
    (∫ z, stencilMatrixKernel p T x₀ h ℓ r ν ω z ^ 2 ∂M.sampleLaw (StencilRole d p)) ≤
      (Fintype.card (StencilRole d p) : ℝ) ^ 2 *
        (Measure.pi (fun _ : StencilRole d p => M.design)).real (acceptedStencil p T x₀ h ℓ r) := by
  let E := acceptedObservationStencil p T x₀ h ℓ r
  have hE : MeasurableSet E := acceptedObservationStencil_measurable p T x₀ h ℓ r
  have hK := M.stencilMatrixKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh ν ω
  have he : (M.sampleLaw (StencilRole d p)).real E =
      (Measure.pi (fun _ : StencilRole d p => M.design)).real (acceptedStencil p T x₀ h ℓ r) := by
    apply congrArg ENNReal.toReal
    exact (M.sampleLaw_design_measurePreserving (StencilRole d p)).measure_preimage
      (acceptedStencil_measurable p T x₀ h ℓ r).nullMeasurableSet
  calc
    _ ≤ ∫ z, E.indicator (fun _ => (Fintype.card (StencilRole d p) : ℝ) ^ 2) z
        ∂M.sampleLaw (StencilRole d p) := by
      apply integral_mono hK.integrable_sq ((integrable_const _).indicator hE)
      intro z
      by_cases hz : z ∈ E
      · rw [Set.indicator_of_mem hz]
        exact stencilMatrixKernel_sq_le p T x₀ hx hh hhsmall hℓ hℓr hrh ν ω z
      · rw [Set.indicator_of_not_mem hz]
        change stencilMatrixKernel p T x₀ h ℓ r ν ω z ^ 2 ≤ 0
        rw [stencilMatrixKernel_off p T x₀ h ℓ r ν ω z hz]
        norm_num
    _ = _ := by rw [integral_indicator_const _ hE]; simp only [smul_eq_mul, he, mul_comm]

end CausalLowerbound.UpperBound.RealOutcomeModel

import CausalLowerbound.UpperBound.PopulationResidual

/-! Conditional expectations of the actual nonsymmetric matrix kernel.
The binary-treatment covariance is diagonal after conditioning on the entire
covariate tuple, even when the weights and features depend on that tuple. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {I : Type*} [Fintype I]

def matrixPopulationValue (w π φ : I → ℝ) : ℝ :=
  (∑ i, w i * π i) * (∑ i, w i * π i * φ i) +
    ∑ i, w i ^ 2 * π i * (1 - π i) * φ i

namespace RealOutcomeModel

variable {d : Type*} [Fintype d] {ε lower upper M₂ : ℝ}
variable (M : RealOutcomeModel d ε lower upper M₂)

theorem conditional_treatment_covariance :
    ∀ᵐ x ∂M.design, covariance (M.conditional x) treatmentValue treatmentValue =
      M.propensity x * (1 - M.propensity x) := by
  filter_upwards [M.treatment_mean] with x hx
  unfold covariance
  simp only [← pow_two, treatmentValue_sq, hx]
  ring

theorem conditional_treatmentContrast_product_identity :
    ∀ᵐ X ∂Measure.pi (fun _ : I => M.design), ∀ w φ : I → ℝ,
      (∫ z, (∑ i, w i * treatmentValue (z i)) *
          (∑ i, w i * treatmentValue (z i) * φ i) ∂M.conditionalTupleLaw X) =
        matrixPopulationValue w (fun i => M.propensity (X i)) φ := by
  have hg := M.treatment_mean.and M.conditional_treatment_covariance
  have htuple : ∀ᵐ X ∂Measure.pi (fun _ : I => M.design), ∀ i,
      (∫ z, treatmentValue z ∂M.conditional (X i)) = M.propensity (X i) ∧
      covariance (M.conditional (X i)) treatmentValue treatmentValue =
        M.propensity (X i) * (1 - M.propensity (X i)) :=
    ae_all_iff.mpr (fun i =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : I => M.design) (i := i)).eventually hg)
  filter_upwards [htuple] with X hX
  intro w φ
  let μ := fun i => M.conditional (X i)
  have hA (i : I) : MemLp treatmentValue 2 (μ i) := treatmentValue_memLp _
  have hc := covariance_coordinateContrasts μ w (fun i => w i * φ i)
    (fun _ => treatmentValue) (fun _ => treatmentValue) hA hA
  have hm := integral_coordinateContrast μ w (fun _ => treatmentValue) hA
  have hn := integral_coordinateContrast μ (fun i => w i * φ i) (fun _ => treatmentValue) hA
  simp only [μ, fun i => (hX i).1] at hm hn
  rw [covariance, hm, hn] at hc
  have hp : coordinateContrast (fun i => w i * φ i) (fun _ => treatmentValue) =
      (fun z => ∑ i, w i * treatmentValue (z i) * φ i) := by
    funext z
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hd : (∑ i, w i * (w i * φ i) * covariance (μ i) treatmentValue treatmentValue) =
      ∑ i, w i ^ 2 * M.propensity (X i) * (1 - M.propensity (X i)) * φ i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(hX i).2]
    ring
  have hφ : (∑ i, w i * φ i * M.propensity (X i)) =
      ∑ i, w i * M.propensity (X i) * φ i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hp, hd, hφ] at hc
  exact (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)

theorem stencilMatrixKernel_conditional_identity (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) :
    ∀ᵐ X ∂Measure.pi (fun _ : StencilRole d p => M.design), ∀ ν ω : TensorIndex d p,
      (∫ z, stencilMatrixKernel p T x₀ h ℓ r ν ω (fun i => (X i, z i))
        ∂M.conditionalTupleLaw X) =
        if X ∈ acceptedStencil p T x₀ h ℓ r then
          stencilFeatureMean p x₀ h ℓ r X ν *
            matrixPopulationValue (observedStencilWeights p x₀ ℓ r X)
              (fun i => M.propensity (X i)) (fun i => stencilFeature p x₀ h X i ω)
        else 0 := by
  filter_upwards [M.conditional_treatmentContrast_product_identity (I := StencilRole d p)] with X hX
  intro ν ω
  by_cases ha : X ∈ acceptedStencil p T x₀ h ℓ r
  · simp only [stencilMatrixKernel, acceptedObservationStencil, Set.mem_setOf_eq, ha, if_true,
      mul_assoc]
    rw [integral_const_mul]
    simpa only [mul_assoc] using congrArg (fun x => stencilFeatureMean p x₀ h ℓ r X ν * x)
      (hX (observedStencilWeights p x₀ ℓ r X) (fun i => stencilFeature p x₀ h X i ω))
  · simp only [stencilMatrixKernel, acceptedObservationStencil, Set.mem_setOf_eq, ha, if_false,
      integral_zero]

theorem stencilPopulationMatrix_integral (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (ν ω : TensorIndex d p) :
    M.stencilPopulationMatrix p T x₀ h ℓ r ν ω =
      ∫ X, (acceptedStencil p T x₀ h ℓ r).indicator
        (fun X => stencilFeatureMean p x₀ h ℓ r X ν *
          matrixPopulationValue (observedStencilWeights p x₀ ℓ r X)
            (fun i => M.propensity (X i)) (fun i => stencilFeature p x₀ h X i ω)) X
        ∂Measure.pi (fun _ : StencilRole d p => M.design) := by
  rw [stencilPopulationMatrix, M.integral_sampleLaw_via_conditional
    ((M.stencilMatrixKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh ν ω).integrable one_le_two)]
  apply integral_congr_ae
  filter_upwards [M.stencilMatrixKernel_conditional_identity p T x₀ h ℓ r] with X hX
  simpa only [Set.indicator_apply] using hX ν ω

end RealOutcomeModel
end CausalLowerbound.UpperBound

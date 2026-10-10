import CausalLowerbound.UpperBound.StencilCompletion
import CausalLowerbound.UpperBound.AcceptanceProbability
import CausalLowerbound.UpperBound.ProjectionMoment

/-! Completion probabilities under the actual real-outcome observation law.
The geometric restriction depends only on covariates.  Its marginal law is
the product design law, even after fixing every shared observation. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.UpperBound

theorem joinRoles_map {I Z W : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Z] [MeasurableSpace W] (f : Z → W) (S : Finset I)
    (x : {i // i ∈ S} → Z) (y : {i // i ∉ S} → Z) :
    (fun i => f (joinRoles S (x, y) i)) =
      joinRoles S ((fun i => f (x i)), (fun i => f (y i))) := by
  funext i
  by_cases hi : i ∈ S
  · simp only [joinRoles_apply_shared _ _ _ i hi]
  · simp only [joinRoles_apply_missing _ _ _ i hi]

variable {d : Type*} [Fintype d]

def acceptedObservationStencil (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) : Set (StencilRole d p → (d → ℝ) × (Bool × ℝ)) :=
  {z | (fun i => (z i).1) ∈ acceptedStencil p T x₀ h ℓ r}

theorem acceptedObservationStencil_measurable (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) :
    MeasurableSet (acceptedObservationStencil p T x₀ h ℓ r) :=
  (acceptedStencil_measurable p T x₀ h ℓ r).preimage
    (measurable_pi_lambda _ (fun i => (measurable_pi_apply i).fst))

def stencilCompletionProbabilityBound (upper : ℝ) (p : ℕ) (T : StencilTemplate d p)
    (ℓ r : ℝ) (S : Finset (StencilRole d p)) : ℝ :=
  (ENNReal.ofReal upper ^ Fintype.card {i // i ∉ S} *
    stencilCompletionVolumeBound p T ℓ r S).toReal

theorem stencilCompletionProbabilityBound_nonneg (upper : ℝ) (p : ℕ)
    (T : StencilTemplate d p) (ℓ r : ℝ) (S : Finset (StencilRole d p)) :
    0 ≤ stencilCompletionProbabilityBound upper p T ℓ r S := ENNReal.toReal_nonneg

namespace RealOutcomeModel

variable {ε lower upper M₂ : ℝ} (M : RealOutcomeModel d ε lower upper M₂)

theorem sampleLaw_design_measurePreserving (I : Type*) [Fintype I] :
    MeasurePreserving (fun z : I → (d → ℝ) × (Bool × ℝ) => fun i => (z i).1)
      (M.sampleLaw I) (Measure.pi (fun _ : I => M.design)) :=
  measurePreserving_pi _ _ (fun _ => ⟨measurable_fst, M.observationLaw_design_marginal⟩)

theorem completion_observation_eq_design {I : Type*} [Fintype I] [DecidableEq I]
    (E : Set (I → d → ℝ)) (hE : MeasurableSet E) (S : Finset I)
    (x : {i // i ∈ S} → (d → ℝ) × (Bool × ℝ)) :
    (Measure.pi (fun _ : {i // i ∉ S} => M.observationLaw))
        {y | (fun i => (joinRoles S (x, y) i).1) ∈ E} =
      (Measure.pi (fun _ : {i // i ∉ S} => M.design))
        {y | joinRoles S ((fun i => (x i).1), y) ∈ E} := by
  let E' : Set ({i // i ∉ S} → d → ℝ) :=
    {y | joinRoles S ((fun i => (x i).1), y) ∈ E}
  have hE' : MeasurableSet E' := hE.preimage
    ((joinRoles S).measurable.comp (measurable_const.prodMk measurable_id))
  have he : {y | (fun i => (joinRoles S (x, y) i).1) ∈ E} =
      (fun y : {i // i ∉ S} → (d → ℝ) × (Bool × ℝ) => fun i => (y i).1) ⁻¹' E' := by
    ext y
    change ((fun i => Prod.fst (joinRoles S (x, y) i)) ∈ E) ↔ _
    rw [joinRoles_map]
    rfl
  rw [he]
  exact (M.sampleLaw_design_measurePreserving {i // i ∉ S}).measure_preimage hE'.nullMeasurableSet

theorem stencilCompletion_probability_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r)
    (S : Finset (StencilRole d p)) (hS : S.Nonempty)
    (x : {i // i ∈ S} → (d → ℝ) × (Bool × ℝ)) :
    (Measure.pi (fun _ : {i // i ∉ S} => M.observationLaw))
        {y | joinRoles S (x, y) ∈ acceptedObservationStencil p T x₀ h ℓ r} ≤
      ENNReal.ofReal upper ^ Fintype.card {i // i ∉ S} *
        stencilCompletionVolumeBound p T ℓ r S := by
  change (Measure.pi (fun _ : {i // i ∉ S} => M.observationLaw))
    {y | (fun i => (joinRoles S (x, y) i).1) ∈ acceptedStencil p T x₀ h ℓ r} ≤ _
  rw [M.completion_observation_eq_design _ (acceptedStencil_measurable p T x₀ h ℓ r)]
  calc
    _ ≤ ENNReal.ofReal upper ^ Fintype.card {i // i ∉ S} *
        volume {y | joinRoles S ((fun i => (x i).1), y) ∈ acceptedStencil p T x₀ h ℓ r} := by
      have hu := M.design_product_upper_domination {i // i ∉ S}
        {y | joinRoles S ((fun i => (x i).1), y) ∈ acceptedStencil p T x₀ h ℓ r}
      simpa only [Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_pow, ENNReal.ofReal] using hu
    _ ≤ _ := mul_le_mul_left'
      (stencilCompletion_volume_le p T x₀ hh hℓ hr S hS (fun i => (x i).1)) _

theorem stencilCompletion_probability_real_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r)
    (S : Finset (StencilRole d p)) (hS : S.Nonempty)
    (x : {i // i ∈ S} → (d → ℝ) × (Bool × ℝ)) :
    (Measure.pi (fun _ : {i // i ∉ S} => M.observationLaw)).real
        {y | joinRoles S (x, y) ∈ acceptedObservationStencil p T x₀ h ℓ r} ≤
      stencilCompletionProbabilityBound upper p T ℓ r S := by
  apply ENNReal.toReal_mono _ (M.stencilCompletion_probability_le p T x₀ hh hℓ hr S hS x)
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (stencilCompletionVolumeBound_ne_top p T ℓ r S)

theorem stencilProjection_secondMoment_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r)
    {K : (StencilRole d p → (d → ℝ) × (Bool × ℝ)) → ℝ}
    (hK : MemLp K 2 (M.sampleLaw (StencilRole d p)))
    (hs : ∀ z, z ∉ acceptedObservationStencil p T x₀ h ℓ r → K z = 0)
    (S : Finset (StencilRole d p)) (hS : S.Nonempty) :
    (∫ x, roleProjection M.observationLaw K S x ^ 2
        ∂Measure.pi (fun _ : {i // i ∈ S} => M.observationLaw)) ≤
      stencilCompletionProbabilityBound upper p T ℓ r S *
        ∫ z, K z ^ 2 ∂M.sampleLaw (StencilRole d p) := by
  exact roleProjection_secondMoment_le_completion_mass M.observationLaw hK
    (acceptedObservationStencil p T x₀ h ℓ r) hs S
    (Filter.Eventually.of_forall (M.stencilCompletion_probability_real_le p T x₀ hh hℓ hr S hS))

end RealOutcomeModel
end CausalLowerbound.UpperBound

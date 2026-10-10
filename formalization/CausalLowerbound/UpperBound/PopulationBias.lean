import CausalLowerbound.UpperBound.PopulationResidual
import CausalLowerbound.UpperBound.ScoreBias
import CausalLowerbound.UpperBound.TaylorApproximation

/-! The population bias bound for the actual estimating equation.  The
coefficient vector is the effect's concrete Taylor vector.  No population
bias assumption is supplied: conditional score algebra, local regularity,
boundary geometry and the design density bound imply it. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

def stencilNuisanceBound (p : ℕ) (T : StencilTemplate d p) (a C ℓ r : ℝ) : ℝ :=
  C * (1 + Fintype.card (TensorIndex d p) * T.inverseBound) * twoScaleModulus a ℓ r

theorem stencilNuisanceBound_nonneg (p : ℕ) (T : StencilTemplate d p) (a : ℝ)
    {C ℓ r : ℝ} (hC : 0 ≤ C) (hℓ : 0 ≤ ℓ) (hr : 0 ≤ r) :
    0 ≤ stencilNuisanceBound p T a C ℓ r := by
  have hi := T.inverseBound_pos.le
  exact mul_nonneg (mul_nonneg hC (by positivity)) (twoScaleModulus_nonneg a ℓ r hℓ hr)

namespace RealOutcomeModel

variable {ε lower upper M₂ : ℝ} (M : RealOutcomeModel d ε lower upper M₂)

theorem stencilResidualKernel_conditional_identity (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) :
    ∀ᵐ X ∂Measure.pi (fun _ : StencilRole d p => M.design),
      ∀ (θ : TensorIndex d p → ℝ) (ν : TensorIndex d p),
        (∫ z, stencilResidualKernel p T x₀ h ℓ r θ ν (fun i => (X i, z i))
          ∂M.conditionalTupleLaw X) =
          if X ∈ acceptedStencil p T x₀ h ℓ r then
            stencilFeatureMean p x₀ h ℓ r X ν *
              scorePopulationValue (observedStencilWeights p x₀ ℓ r X)
                (fun i => M.propensity (X i)) (fun i => M.baseline (X i))
                (fun i => M.effect (X i) - ∑ ω, θ ω * stencilFeature p x₀ h X i ω)
          else 0 := by
  filter_upwards [M.conditional_residualScore_identity (I := StencilRole d p)] with X hX
  intro θ ν
  by_cases ha : X ∈ acceptedStencil p T x₀ h ℓ r
  · simp only [stencilResidualKernel_eq_score, acceptedObservationStencil, Set.mem_setOf_eq, ha, if_true]
    rw [integral_const_mul, hX]
  · simp only [stencilResidualKernel_eq_score, acceptedObservationStencil, Set.mem_setOf_eq, ha, if_false,
      integral_zero]

theorem stencilPopulationResidual_coordinate_bound (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (hε : 0 ≤ ε)
    (θ : TensorIndex d p → ℝ) {A B R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hπ : ∀ X ∈ acceptedStencil p T x₀ h ℓ r, |∑ i, observedStencilWeights p x₀ ℓ r X i * M.propensity (X i)| ≤ A)
    (hμ : ∀ X ∈ acceptedStencil p T x₀ h ℓ r, |∑ i, observedStencilWeights p x₀ ℓ r X i * M.baseline (X i)| ≤ B)
    (hτ : ∀ X ∈ acceptedStencil p T x₀ h ℓ r, ∀ i,
      |M.effect (X i) - ∑ ω, θ ω * stencilFeature p x₀ h X i ω| ≤ R) (ν : TensorIndex d p) :
    |M.stencilPopulationResponse p T x₀ h ℓ r ν -
        ∑ ω, M.stencilPopulationMatrix p T x₀ h ℓ r ν ω * θ ω| ≤
      (A * B + ((Fintype.card (StencilRole d p) : ℝ) ^ 2 + 1) * R) *
        (Measure.pi (fun _ : StencilRole d p => M.design)).real (acceptedStencil p T x₀ h ℓ r) := by
  rw [← M.stencilPopulationResidual_integral p T x₀ hx hh hhsmall hℓ hℓr hrh θ ν,
    M.integral_sampleLaw_via_conditional
      ((M.stencilResidualKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh θ ν).integrable one_le_two)]
  let C := A * B + ((Fintype.card (StencilRole d p) : ℝ) ^ 2 + 1) * R
  have hbound : ∀ᵐ X ∂Measure.pi (fun _ : StencilRole d p => M.design),
      ‖∫ z, stencilResidualKernel p T x₀ h ℓ r θ ν (fun i => (X i, z i)) ∂M.conditionalTupleLaw X‖ ≤
        (acceptedStencil p T x₀ h ℓ r).indicator (fun _ => C) X := by
    filter_upwards [M.stencilResidualKernel_conditional_identity p T x₀ h ℓ r,
      M.tuple_propensity_mem_unit (I := StencilRole d p) hε] with X hX hπX
    rw [hX θ ν, Real.norm_eq_abs]
    by_cases ha : X ∈ acceptedStencil p T x₀ h ℓ r
    · rw [if_pos ha, Set.indicator_of_mem ha, abs_mul]
      have hm := stencilFeatureMean_bound p x₀ h ℓ r X ν
        (fun i => acceptedStencil_feature_bound p T x₀ hx hh hhsmall hℓ hℓr hrh X ha i ν)
      have hs := scorePopulationValue_bound (observedStencilWeights p x₀ ℓ r X)
        (fun i => M.propensity (X i)) (fun i => M.baseline (X i))
        (fun i => M.effect (X i) - ∑ ω, θ ω * stencilFeature p x₀ h X i ω)
        (observedStencilWeights_norm_sq p x₀ ℓ r X) hπX hA hR (hπ X ha) (hμ X ha) (hτ X ha)
      exact (mul_le_of_le_one_left (abs_nonneg _) hm).trans hs
    · simp only [if_neg ha, Set.indicator_of_not_mem ha, abs_zero, le_refl]
  have he := norm_integral_le_of_norm_le
    ((integrable_const C).indicator (acceptedStencil_measurable p T x₀ h ℓ r)) hbound
  rw [integral_indicator_const _ (acceptedStencil_measurable p T x₀ h ℓ r)] at he
  simpa only [Real.norm_eq_abs, smul_eq_mul, C, mul_comm] using he

theorem stencilPopulationResidual_bias (p qα qβ qγ : ℕ) (hαp : qα ≤ p) (hβp : qβ ≤ p) (hγp : qγ ≤ p)
    (T : StencilTemplate d p) (x₀ : d → ℝ) {h ℓ r θα θβ θγ Lπ L₀ Lτ : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (hε : 0 ≤ ε) (hupper : 0 ≤ upper)
    {U : Set (d → ℝ)} (hU : IsOpen U) (hcube : Icc (0 : d → ℝ) 1 ⊆ U)
    (hreg : M.LocalRegularity U qα qβ qγ θα θβ θγ Lπ L₀ Lτ)
    (hLπ : 0 ≤ Lπ) (hL₀ : 0 ≤ L₀) (hLτ : 0 ≤ Lτ)
    (hθα : 0 ≤ θα) (hθβ : 0 ≤ θβ) (hθγ : 0 ≤ θγ) :
    ‖M.stencilPopulationResponse p T x₀ h ℓ r -
        (M.stencilPopulationMatrix p T x₀ h ℓ r) *ᵥ
          stencilTaylorCoefficients p qγ hγp M.effect x₀ h‖ ≤
      (stencilNuisanceBound p T ((qα : ℝ) + θα) Lπ ℓ r *
          stencilNuisanceBound p T ((qβ : ℝ) + θβ) L₀ ℓ r +
        ((Fintype.card (StencilRole d p) : ℝ) ^ 2 + 1) * (Lτ * h ^ ((qγ : ℝ) + θγ))) *
        upper ^ Fintype.card (StencilRole d p) * stencilMass p T h ℓ r := by
  rcases hreg with ⟨hπ, hπholder, hμ, hμholder, hτ, hτholder⟩
  let A := stencilNuisanceBound p T ((qα : ℝ) + θα) Lπ ℓ r
  let B := stencilNuisanceBound p T ((qβ : ℝ) + θβ) L₀ ℓ r
  let R := Lτ * h ^ ((qγ : ℝ) + θγ)
  have hA : 0 ≤ A := stencilNuisanceBound_nonneg p T _ hLπ hℓ.le (hℓ.trans_le hℓr).le
  have hB : 0 ≤ B := stencilNuisanceBound_nonneg p T _ hL₀ hℓ.le (hℓ.trans_le hℓr).le
  have hR : 0 ≤ R := mul_nonneg hLτ (Real.rpow_nonneg hh.le _)
  have hC : 0 ≤ A * B + ((Fintype.card (StencilRole d p) : ℝ) ^ 2 + 1) * R := by positivity
  apply (pi_norm_le_iff_of_nonneg (by
    change 0 ≤ (A * B + ((Fintype.card (StencilRole d p) : ℝ) ^ 2 + 1) * R) *
      upper ^ Fintype.card (StencilRole d p) * stencilMass p T h ℓ r
    exact mul_nonneg (mul_nonneg hC (pow_nonneg hupper _)) (stencilMass_pos p T hh hℓ (hℓ.trans_le hℓr)).le)).mpr
  intro ν
  change |M.stencilPopulationResponse p T x₀ h ℓ r ν -
    ∑ ω, M.stencilPopulationMatrix p T x₀ h ℓ r ν ω * stencilTaylorCoefficients p qγ hγp M.effect x₀ h ω| ≤ _
  have hb := M.stencilPopulationResidual_coordinate_bound p T x₀ hx hh hhsmall hℓ hℓr hrh hε
    (stencilTaylorCoefficients p qγ hγp M.effect x₀ h) hA hR
    (fun X hX => acceptedStencil_contrast_bound p qα hαp T x₀ hx hh hhsmall hℓ hℓr hrh
      X hX M.propensity hU hcube hπ hπholder hLπ hθα)
    (fun X hX => acceptedStencil_contrast_bound p qβ hβp T x₀ hx hh hhsmall hℓ hℓr hrh
      X hX M.baseline hU hcube hμ hμholder hL₀ hθβ)
    (fun X hX i => acceptedStencil_taylor_error p qγ hγp T M.effect x₀ hx hh hhsmall hℓ hℓr hrh
      hU hcube hτ hτholder hLτ hθγ X hX i) ν
  apply hb.trans
  simpa only [A, B, R, stencilNuisanceBound, mul_assoc] using
    mul_le_mul_of_nonneg_left
      (M.acceptedStencil_probability_real_le_mass p T x₀ hh hℓ (hℓ.trans_le hℓr) hupper) hC

end RealOutcomeModel
end CausalLowerbound.UpperBound

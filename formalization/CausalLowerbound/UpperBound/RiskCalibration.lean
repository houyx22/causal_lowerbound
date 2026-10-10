import CausalLowerbound.UpperBound.EstimatorRisk

/-! A fixed inverse cutoff, obtained from the proved population coercivity.
It depends only on class parameters and the stencil, before any model,
target, sample or bandwidth is supplied. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d] {ε lower upper M₂ : ℝ}

def stencilCutoffConstant (p : ℕ) (T : StencilTemplate d p)
    (hε : 0 < ε) (hε1 : ε < 1) (hlower : 0 < lower) (hupper : 0 ≤ upper) : ℝ :=
  (exists_stencilPopulationMatrix_lower (M₂ := M₂) p T hε hε1 hlower hupper).choose / 4

theorem stencilCutoffConstant_pos (p : ℕ) (T : StencilTemplate d p)
    (hε : 0 < ε) (hε1 : ε < 1) (hlower : 0 < lower) (hupper : 0 ≤ upper) :
    0 < stencilCutoffConstant (M₂ := M₂) p T hε hε1 hlower hupper :=
  div_pos (exists_stencilPopulationMatrix_lower (M₂ := M₂) p T hε hε1 hlower hupper).choose_spec.1
    (by norm_num)

def stencilMatrixErrorSize (p : ℕ) (T : StencilTemplate d p) (α Lπ upper h ℓ r : ℝ) : ℝ :=
  Fintype.card (TensorIndex d p) *
    ((stencilNuisanceBound p T α Lπ ℓ r *
      (stencilNuisanceBound p T α Lπ ℓ r + stencilFeatureVariationBound p T h ℓ) +
        2 * stencilFeatureVariationBound p T h ℓ) * upper ^ Fintype.card (StencilRole d p))

namespace RealOutcomeModel

variable (M : RealOutcomeModel d ε lower upper M₂)

theorem stencilPopulationMatrix_calibrated_lower (p q : ℕ) (hqp : q ≤ p)
    (T : StencilTemplate d p) (x₀ : d → ℝ) {h ℓ r θ Lπ : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hlower : 0 < lower) (hupper : 0 ≤ upper)
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    {U : Set (d → ℝ)} (hU : IsOpen U) (hcube : Icc (0 : d → ℝ) 1 ⊆ U)
    (hreg : ContDiffOn ℝ q M.propensity U) (hholder : HolderControlOn q θ Lπ M.propensity U)
    (hLπ : 0 ≤ Lπ) (hθ : 0 ≤ θ)
    (hsmall : stencilMatrixErrorSize p T ((q : ℝ) + θ) Lπ upper h ℓ r ≤
      2 * stencilCutoffConstant (M₂ := M₂) p T hε hε1 hlower hupper) :
    ∀ v : TensorIndex d p → ℝ,
      (2 * (stencilCutoffConstant (M₂ := M₂) p T hε hε1 hlower hupper * stencilMass p T h ℓ r)) * ‖v‖ ≤
        ‖M.stencilPopulationMatrix p T x₀ h ℓ r *ᵥ v‖ := by
  have hs := (exists_stencilPopulationMatrix_lower (M₂ := M₂) p T hε hε1 hlower hupper).choose_spec.2
  have hA := stencilNuisanceBound_nonneg p T ((q : ℝ) + θ) hLπ hℓ.le (hℓ.trans_le hℓr).le
  have hc (X : StencilRole d p → d → ℝ) (hX : X ∈ acceptedStencil p T x₀ h ℓ r) :=
    acceptedStencil_contrast_bound p q hqp T x₀ hx hh hhsmall hℓ hℓr hrh X hX
      M.propensity hU hcube hreg hholder hLπ hθ
  have hsmall' : stencilMatrixErrorSize p T ((q : ℝ) + θ) Lπ upper h ℓ r ≤
      (exists_stencilPopulationMatrix_lower (M₂ := M₂) p T hε hε1 hlower hupper).choose / 2 := by
    unfold stencilCutoffConstant at hsmall
    linarith
  intro v
  have hv := hs M x₀ h ℓ r (stencilNuisanceBound p T ((q : ℝ) + θ) Lπ ℓ r)
    hx hh hhsmall hℓ hℓr hrh hA hc hsmall' v
  convert hv using 1 <;> unfold stencilCutoffConstant <;> ring

end RealOutcomeModel
end CausalLowerbound.UpperBound

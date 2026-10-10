import CausalLowerbound.UpperBound.LeadingGram
import CausalLowerbound.UpperBound.MatrixOperators

/-! Uniform lower operator bounds for the leading Gram matrix and the actual
population estimating matrix.  The constants are chosen before the model,
target and bandwidths.  The remaining smallness condition is explicit. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d] {ε lower upper M₂ : ℝ}

theorem exists_stencilLeadingGram_lower (p : ℕ) (T : StencilTemplate d p)
    (hε : 0 < ε) (hε1 : ε < 1) (hlower : 0 < lower) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : RealOutcomeModel d ε lower upper M₂) (x₀ : d → ℝ)
      (h ℓ r : ℝ), (∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) → 0 < h → h ≤ 1 / 2 →
      0 < ℓ → ℓ ≤ r → r ≤ h / 4 → ∀ θ : TensorIndex d p → ℝ,
        (c * stencilMass p T h ℓ r) * ‖θ‖ ≤ ‖M.stencilLeadingGram p T x₀ h ℓ r *ᵥ θ‖ := by
  obtain ⟨κ, hκ, hgram⟩ := exists_tensorGram_lower_bound (d := d) p
  let b := ε * (1 - ε) * lower ^ Fintype.card (StencilRole d p) * (4 : ℝ) ^ Fintype.card d
  have hb : 0 < b := by
    have he : 0 < 1 - ε := sub_pos.mpr hε1
    dsimp [b]
    positivity
  have hK : (0 : ℝ) < Fintype.card (TensorIndex d p) := by exact_mod_cast Fintype.card_pos
  let c := b * κ / Fintype.card (TensorIndex d p)
  refine ⟨c, div_pos (mul_pos hb hκ) hK, ?_⟩
  intro M x₀ h ℓ r hx hh hhsmall hℓ hℓr hrh θ
  have hmass := stencilMass_pos p T hh hℓ (hℓ.trans_le hℓr)
  have hquad (u : TensorIndex d p → ℝ) :
      (b * stencilMass p T h ℓ r * κ) * ‖u‖ ^ 2 ≤
        ∑ ν, u ν * (M.stencilLeadingGram p T x₀ h ℓ r *ᵥ u) ν := by
    calc
      _ = (b * stencilMass p T h ℓ r) * (κ * ‖u‖ ^ 2) := by ring
      _ ≤ (b * stencilMass p T h ℓ r) * tensorGramEnergy p u :=
        mul_le_mul_of_nonneg_left (hgram u) (mul_pos hb hmass).le
      _ ≤ _ := M.stencilLeadingGram_quadratic_lower p T x₀ hx hh hhsmall hℓ hℓr hrh
        hε.le hε1.le hlower.le u
  have he := matrix_lower_of_quadratic (M.stencilLeadingGram p T x₀ h ℓ r)
    (b * stencilMass p T h ℓ r * κ) hquad θ
  convert he using 1 <;> dsimp [c] <;> ring

theorem exists_stencilPopulationMatrix_lower (p : ℕ) (T : StencilTemplate d p)
    (hε : 0 < ε) (hε1 : ε < 1) (hlower : 0 < lower) (hupper : 0 ≤ upper) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : RealOutcomeModel d ε lower upper M₂) (x₀ : d → ℝ)
      (h ℓ r A : ℝ), (∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) → 0 < h → h ≤ 1 / 2 →
      0 < ℓ → ℓ ≤ r → r ≤ h / 4 → 0 ≤ A →
      (∀ X ∈ acceptedStencil p T x₀ h ℓ r,
        |∑ i, observedStencilWeights p x₀ ℓ r X i * M.propensity (X i)| ≤ A) →
      (Fintype.card (TensorIndex d p) *
        ((A * (A + stencilFeatureVariationBound p T h ℓ) + 2 * stencilFeatureVariationBound p T h ℓ) *
          upper ^ Fintype.card (StencilRole d p)) ≤ c / 2) →
      ∀ θ : TensorIndex d p → ℝ,
        (c / 2 * stencilMass p T h ℓ r) * ‖θ‖ ≤ ‖M.stencilPopulationMatrix p T x₀ h ℓ r *ᵥ θ‖ := by
  obtain ⟨c, hc, hlead⟩ := exists_stencilLeadingGram_lower (upper := upper) (M₂ := M₂) p T hε hε1 hlower
  refine ⟨c, hc, ?_⟩
  intro M x₀ h ℓ r A hx hh hhsmall hℓ hℓr hrh hA hcontrast hsmall θ
  let E := (A * (A + stencilFeatureVariationBound p T h ℓ) + 2 * stencilFeatureVariationBound p T h ℓ) *
    upper ^ Fintype.card (StencilRole d p)
  have hV := stencilFeatureVariationBound_nonneg p T hh.le hℓ.le
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hmass := stencilMass_pos p T hh hℓ (hℓ.trans_le hℓr)
  have hp := matrix_lower_of_entry_perturbation (M.stencilLeadingGram p T x₀ h ℓ r)
    (M.stencilPopulationMatrix p T x₀ h ℓ r) (c * stencilMass p T h ℓ r)
    (mul_nonneg hE hmass.le) (hlead M x₀ h ℓ r hx hh hhsmall hℓ hℓr hrh)
    (fun ν ω => M.stencilPopulationMatrix_perturbation p T x₀ hx hh hhsmall hℓ hℓr hrh
      hε.le hupper hA hcontrast ν ω) θ
  apply le_trans _ hp
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg θ)
  have hs : Fintype.card (TensorIndex d p) * E ≤ c / 2 := hsmall
  nlinarith [mul_le_mul_of_nonneg_right hs hmass.le]

end CausalLowerbound.UpperBound

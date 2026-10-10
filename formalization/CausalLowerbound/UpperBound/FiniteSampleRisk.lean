import CausalLowerbound.UpperBound.RiskCalibration
import CausalLowerbound.UpperBound.SampleEstimator

/-! Finite-sample risk for the constructed estimator under the original iid
sample law.  Matrix coercivity, bias, measurability and all empirical moments
are consequences of the model and local smoothness.  Only explicit geometric
and numerical bandwidth conditions remain. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

def stencilMseEnvelope (p qγ : ℕ) (T : StencilTemplate d p)
    (α β γ Lπ L₀ Lτ upper M₂ B c h ℓ r η : ℝ) : ℝ :=
  3 / c ^ 2 * (stencilBiasSize p T α β γ Lπ L₀ Lτ upper h ℓ r ^ 2 +
    (stencilResponseMomentConstant (d := d) p upper M₂ B +
      9 * stencilEffectCoefficientBound (d := d) qγ Lτ ^ 2 *
        stencilMatrixMomentConstant (d := d) p upper B) * stencilVarianceTerm (d := d) h ℓ η)

namespace RealOutcomeModel

variable {ε lower upper M₂ : ℝ} (M : RealOutcomeModel d ε lower upper M₂)

theorem sampleStencilEstimate_risk_bound
    (p qα qβ qγ : ℕ) (hαp : qα ≤ p) (hβp : qβ ≤ p) (hγp : qγ ≤ p)
    (T : StencilTemplate d p) (x₀ : d → ℝ) {h ℓ r θα θβ θγ Lπ L₀ Lτ B : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hlower : 0 < lower) (hupper : 0 ≤ upper)
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    {U : Set (d → ℝ)} (hU : IsOpen U) (hcube : Icc (0 : d → ℝ) 1 ⊆ U)
    (hreg : M.LocalRegularity U qα qβ qγ θα θβ θγ Lπ L₀ Lτ)
    (hLπ : 0 ≤ Lπ) (hL₀ : 0 ≤ L₀) (hLτ : 0 ≤ Lτ)
    (hθα : 0 ≤ θα) (hθβ : 0 ≤ θβ) (hθγ : 0 ≤ θγ)
    (n : ℕ) (hn : Fintype.card (StencilRole d p) ≤ n) (hB : 1 ≤ B) (hUB : upper ≤ B)
    (hcoarse : 2 * Fintype.card (StencilRole d p) / (n : ℝ) ≤ B * (coarseCellVolume p T r).toReal)
    (hsmall : stencilMatrixErrorSize p T ((qα : ℝ) + θα) Lπ upper h ℓ r ≤
      2 * stencilCutoffConstant (M₂ := M₂) p T hε hε1 hlower hupper) :
    let c := stencilCutoffConstant (M₂ := M₂) p T hε hε1 hlower hupper
    let hκ := mul_pos (stencilCutoffConstant_pos (M₂ := M₂) p T hε hε1 hlower hupper)
      (stencilMass_pos p T hh hℓ (hℓ.trans_le hℓr))
    let est := sampleStencilEstimate p T x₀ h ℓ r n (c * stencilMass p T h ℓ r) hκ
      (stencilEffectCoefficientBound (d := d) qγ Lτ)
    let E := stencilMseEnvelope p qγ T ((qα : ℝ) + θα) ((qβ : ℝ) + θβ) ((qγ : ℝ) + θγ)
      Lπ L₀ Lτ upper M₂ B c h ℓ r (2 * Fintype.card (StencilRole d p) / n)
    (∫ z, (est z - M.effect x₀) ^ 2 ∂M.sampleLaw (Fin n)) ≤ E ∧
      (∫ z, |est z - M.effect x₀| ∂M.sampleLaw (Fin n)) ≤ Real.sqrt E := by
  dsimp only
  let c := stencilCutoffConstant (M₂ := M₂) p T hε hε1 hlower hupper
  have hc : 0 < c := stencilCutoffConstant_pos p T hε hε1 hlower hupper
  have hκ := mul_pos hc (stencilMass_pos p T hh hℓ (hℓ.trans_le hℓr))
  have hL := stencilEffectCoefficientBound_nonneg (d := d) qγ hLτ
  let J : StencilRole d p → Type := fun _ => Fin (balancedGroupSize (StencilRole d p) n)
  letI : Nonempty (Fin (balancedGroupSize (StencilRole d p) n)) :=
    ⟨⟨0, balancedGroupSize_pos (StencilRole d p) hn⟩⟩
  have hQ := M.stencilPopulationMatrix_calibrated_lower p qα hαp T x₀ hε hε1 hlower hupper
    hx hh hhsmall hℓ hℓr hrh hU hcube hreg.1 hreg.2.1 hLπ hθα hsmall
  have he := M.empiricalStencilEstimate_mse_bound_of_lower p qα qβ qγ hαp hβp hγp T x₀
    hx hh hhsmall hℓ hℓr hrh hε.le hupper hU hcube hreg hLπ hL₀ hLτ hθα hθβ hθγ hc J
    (η := 2 * Fintype.card (StencilRole d p) / (n : ℝ)) (by positivity) hB hUB hcoarse
    (fun _ => balancedGroupSize_inv_le (StencilRole d p) hn) hQ
  have hs := sampleStencilEstimate_mse_eq p T x₀ h ℓ r n hκ
    (stencilEffectCoefficientBound (d := d) qγ Lτ) (M.effect x₀) M.observationLaw
  have hm : (∫ z, (sampleStencilEstimate p T x₀ h ℓ r n (c * stencilMass p T h ℓ r) hκ
      (stencilEffectCoefficientBound (d := d) qγ Lτ) z - M.effect x₀) ^ 2 ∂M.sampleLaw (Fin n)) ≤
      stencilMseEnvelope p qγ T ((qα : ℝ) + θα) ((qβ : ℝ) + θβ) ((qγ : ℝ) + θγ)
        Lπ L₀ Lτ upper M₂ B c h ℓ r (2 * Fintype.card (StencilRole d p) / n) := by
    rw [sampleLaw, hs]
    exact he
  refine ⟨hm, ?_⟩
  exact (sampleStencilEstimate_mae_le_sqrt_mse p T x₀ h ℓ r n hκ hL
    (M.effect x₀) M.observationLaw).trans (Real.sqrt_le_sqrt hm)

end RealOutcomeModel
end CausalLowerbound.UpperBound

import CausalLowerbound.UpperBound.EmpiricalMoments
import CausalLowerbound.UpperBound.PopulationCoercivity
import CausalLowerbound.UpperBound.RiskNormalization

/-! Quantitative risk of the concrete estimator at admissible bandwidths.
The Taylor vector, population bias, measurable inverse and empirical moments
are all supplied by the proved construction. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

def stencilEffectCoefficientBound (q : ℕ) (L : ℝ) : ℝ :=
  L * ∑ k : Fin (q + 1), (Fintype.card d : ℝ) ^ k.val

def stencilBiasSize (p : ℕ) (T : StencilTemplate d p)
    (α β γ Lπ L₀ Lτ upper h ℓ r : ℝ) : ℝ :=
  (stencilNuisanceBound p T α Lπ ℓ r * stencilNuisanceBound p T β L₀ ℓ r +
    ((Fintype.card (StencilRole d p) : ℝ) ^ 2 + 1) * (Lτ * h ^ γ)) *
      upper ^ Fintype.card (StencilRole d p)

def stencilResponseMomentConstant (p : ℕ) (upper M₂ B : ℝ) : ℝ :=
  Fintype.card (TensorIndex d p) * ((2 : ℝ) ^ Fintype.card (StencilRole d p) *
    B ^ Fintype.card (StencilRole d p) *
      (2 * M₂ * (Fintype.card (StencilRole d p) : ℝ) ^ 2 * upper ^ Fintype.card (StencilRole d p)))

def stencilMatrixMomentConstant (p : ℕ) (upper B : ℝ) : ℝ :=
  (Fintype.card (TensorIndex d p) : ℝ) ^ 4 * ((2 : ℝ) ^ Fintype.card (StencilRole d p) *
    B ^ Fintype.card (StencilRole d p) *
      ((Fintype.card (StencilRole d p) : ℝ) ^ 2 * upper ^ Fintype.card (StencilRole d p)))

def stencilVarianceTerm (h ℓ η : ℝ) : ℝ :=
  η / (h / 4) ^ Fintype.card d + η ^ 2 / ((h / 4) ^ Fintype.card d * ℓ ^ Fintype.card d)

theorem stencilEffectCoefficientBound_nonneg (q : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ stencilEffectCoefficientBound (d := d) q L := by unfold stencilEffectCoefficientBound; positivity

theorem stencilBiasSize_nonneg (p : ℕ) (T : StencilTemplate d p)
    (α β γ : ℝ) {Lπ L₀ Lτ upper h ℓ r : ℝ}
    (hLπ : 0 ≤ Lπ) (hL₀ : 0 ≤ L₀) (hLτ : 0 ≤ Lτ) (hupper : 0 ≤ upper)
    (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ) (hr : 0 ≤ r) :
    0 ≤ stencilBiasSize p T α β γ Lπ L₀ Lτ upper h ℓ r := by
  have hA := stencilNuisanceBound_nonneg p T α hLπ hℓ hr
  have hB := stencilNuisanceBound_nonneg p T β hL₀ hℓ hr
  unfold stencilBiasSize
  positivity

namespace RealOutcomeModel

variable {ε lower upper M₂ : ℝ} (M : RealOutcomeModel d ε lower upper M₂)

theorem empiricalStencilEstimate_mse_bound_of_lower
    (p qα qβ qγ : ℕ) (hαp : qα ≤ p) (hβp : qβ ≤ p) (hγp : qγ ≤ p)
    (T : StencilTemplate d p) (x₀ : d → ℝ) {h ℓ r θα θβ θγ Lπ L₀ Lτ c : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (hε : 0 ≤ ε) (hupper : 0 ≤ upper)
    {U : Set (d → ℝ)} (hU : IsOpen U) (hcube : Icc (0 : d → ℝ) 1 ⊆ U)
    (hreg : M.LocalRegularity U qα qβ qγ θα θβ θγ Lπ L₀ Lτ)
    (hLπ : 0 ≤ Lπ) (hL₀ : 0 ≤ L₀) (hLτ : 0 ≤ Lτ)
    (hθα : 0 ≤ θα) (hθβ : 0 ≤ θβ) (hθγ : 0 ≤ θγ) (hc : 0 < c)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)] [∀ i, Nonempty (J i)]
    {η B : ℝ} (hη : 0 ≤ η) (hB : 1 ≤ B) (hUB : upper ≤ B)
    (hηC : η ≤ B * (coarseCellVolume p T r).toReal)
    (hJ : ∀ i, (Fintype.card (J i) : ℝ)⁻¹ ≤ η)
    (hQ : ∀ θ : TensorIndex d p → ℝ,
      (2 * (c * stencilMass p T h ℓ r)) * ‖θ‖ ≤ ‖M.stencilPopulationMatrix p T x₀ h ℓ r *ᵥ θ‖) :
    (∫ z, (empiricalStencilEstimate p T x₀ h ℓ r J (c * stencilMass p T h ℓ r)
      (mul_pos hc (stencilMass_pos p T hh hℓ (hℓ.trans_le hℓr)))
      (stencilEffectCoefficientBound (d := d) qγ Lτ) z - M.effect x₀) ^ 2
        ∂Measure.pi (fun _ : Σ i, J i => M.observationLaw)) ≤
      3 / c ^ 2 *
        (stencilBiasSize p T ((qα : ℝ) + θα) ((qβ : ℝ) + θβ) ((qγ : ℝ) + θγ)
          Lπ L₀ Lτ upper h ℓ r ^ 2 +
          (stencilResponseMomentConstant (d := d) p upper M₂ B +
            9 * stencilEffectCoefficientBound (d := d) qγ Lτ ^ 2 *
              stencilMatrixMomentConstant (d := d) p upper B) * stencilVarianceTerm (d := d) h ℓ η) := by
  let θ := stencilTaylorCoefficients p qγ hγp M.effect x₀ h
  let L := stencilEffectCoefficientBound (d := d) qγ Lτ
  let δ := stencilBiasSize p T ((qα : ℝ) + θα) ((qβ : ℝ) + θβ) ((qγ : ℝ) + θγ) Lπ L₀ Lτ upper h ℓ r
  have hmass := stencilMass_pos p T hh hℓ (hℓ.trans_le hℓr)
  have hL : 0 ≤ L := stencilEffectCoefficientBound_nonneg qγ hLτ
  have hδ : 0 ≤ δ := stencilBiasSize_nonneg p T _ _ _ hLπ hL₀ hLτ hupper hh.le hℓ.le (hℓ.trans_le hℓr).le
  have hθ : ‖θ‖ ≤ L := stencilTaylorCoefficients_local_bound p qγ hγp M.effect x₀
    (hcube ⟨fun i => (hx i).1, fun i => (hx i).2⟩) hh.le (by linarith) hLτ hreg.2.2.2.2.2
  have hproj : ‖(ContinuousLinearMap.proj (0 : TensorIndex d p) : (TensorIndex d p → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
      simpa only [one_mul] using norm_le_pi_norm v (0 : TensorIndex d p))
  have hM₂ := M.responseSecondMoment_nonneg
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  have hV : 0 ≤ stencilVarianceTerm (d := d) h ℓ η := by unfold stencilVarianceTerm; positivity
  have hCb : 0 ≤ stencilResponseMomentConstant (d := d) p upper M₂ B := by
    unfold stencilResponseMomentConstant
    positivity
  have hCQ : 0 ≤ stencilMatrixMomentConstant (d := d) p upper B := by
    unfold stencilMatrixMomentConstant
    positivity
  have hest := (empiricalStencilEstimate_measurable p T x₀ h ℓ r J (mul_pos hc hmass) L).aestronglyMeasurable
    (μ := Measure.pi (fun _ : Σ i, J i => M.observationLaw))
  have hp := M.stencilPopulationResidual_bias p qα qβ qγ hαp hβp hγp T x₀ hx hh hhsmall hℓ hℓr hrh
    hε hupper hU hcube hreg hLπ hL₀ hLτ hθα hθβ hθγ
  have he₀ := clippedEstimate_normalized_mse_bound
    (E := TensorIndex d p → ℝ) (Measure.pi (fun _ : Σ i, J i => M.observationLaw))
    hc hmass hL hδ hV hCb hCQ
    (ContinuousLinearMap.proj (0 : TensorIndex d p)) hproj
    (matrixOperator (M.stencilPopulationMatrix p T x₀ h ℓ r))
    (M.stencilPopulationResponse p T x₀ h ℓ r) θ hθ
    (fun z => matrixOperator (empiricalStencilMatrix p T x₀ h ℓ r J z))
    (empiricalStencilResponse p T x₀ h ℓ r J)
  have he₁ := he₀ hQ
  have hest' : AEStronglyMeasurable
      (fun z => clippedEstimate (c * stencilMass p T h ℓ r) (mul_pos hc hmass) L
        (ContinuousLinearMap.proj (0 : TensorIndex d p))
        (matrixOperator (empiricalStencilMatrix p T x₀ h ℓ r J z))
        (empiricalStencilResponse p T x₀ h ℓ r J z))
      (Measure.pi (fun _ : Σ i, J i => M.observationLaw)) := by
    simp_rw [← empiricalStencilEstimate_eq_clippedEstimate]
    exact hest
  have he₂ := he₁ hest'
  have he₃ := he₂ (M.empiricalStencilResponse_centered_norm_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh J)
  have he₄ := he₃ (M.empiricalStencilMatrix_centered_norm_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh J)
  have he₅ := he₄ (M.empiricalStencilResponse_meanSquare_le p T x₀ hx hh hhsmall hℓ hℓr hrh J hupper hη hB hUB hηC hJ)
  have he₆ := he₅ (M.empiricalStencilMatrix_meanSquare_le p T x₀ hx hh hhsmall hℓ hℓr hrh J hupper hη hB hUB hηC hJ)
  have he := he₆ hp
  simpa only [← empiricalStencilEstimate_eq_clippedEstimate, ContinuousLinearMap.proj_apply, θ,
    stencilTaylorCoefficients_constant, L, δ] using he

end RealOutcomeModel
end CausalLowerbound.UpperBound

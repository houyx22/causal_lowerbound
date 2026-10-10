import CausalLowerbound.UpperBound.PopulationMatrix
import CausalLowerbound.UpperBound.AnchorProjection

/-! Coercivity of the actual leading Gram matrix.  The lower design-density
bound is used as a measure domination, and the full tuple-dependent treatment
variance is kept until its overlap lower bound is applied. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

theorem tensorPolynomial_abs_le_card_norm (p : ℕ) (θ : TensorIndex d p → ℝ)
    (u : d → ℝ) (hu : ‖u‖ ≤ 1) :
    |tensorPolynomial p θ u| ≤ Fintype.card (TensorIndex d p) * ‖θ‖ := by
  calc
    _ ≤ ∑ ν, |θ ν * tensorMonomial p ν u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ν : TensorIndex d p, ‖θ‖ := Finset.sum_le_sum (fun ν _ => by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (tensorMonomial_abs_le_one p ν u hu)).trans
        (norm_le_pi_norm θ ν))
    _ = _ := by simp

theorem anchorUnitBox_norm_le_one (u : d → ℝ) (hu : u ∈ anchorUnitBox d) : ‖u‖ ≤ 1 :=
  nonnegative_coordinate_norm_le zero_le_one (fun i => ⟨hu.1 i, (hu.2 i).trans (by norm_num)⟩)

theorem acceptedAnchorSquare_integrable (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (θ : TensorIndex d p → ℝ)
    (μ : Measure (StencilRole d p → d → ℝ)) [IsFiniteMeasure μ] :
    Integrable ((acceptedStencil p T x₀ h ℓ r).indicator
      (fun X => tensorPolynomial p θ (observedAnchorCoordinate p x₀ h X) ^ 2)) μ := by
  have hm := (((continuous_tensorPolynomial p θ).comp
    (continuous_observedAnchorCoordinate p x₀ h)).pow 2).measurable.indicator
    (acceptedStencil_measurable p T x₀ h ℓ r)
  apply (integrable_const (((Fintype.card (TensorIndex d p) : ℝ) * ‖θ‖) ^ 2)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro X
  by_cases hX : X ∈ acceptedStencil p T x₀ h ℓ r
  · rw [Set.indicator_of_mem hX, Real.norm_eq_abs, abs_sq]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr
      (tensorPolynomial_abs_le_card_norm p θ _ (anchorUnitBox_norm_le_one _ hX.1))
  · rw [Set.indicator_of_not_mem hX, norm_zero]
    positivity

namespace RealOutcomeModel

variable {ε lower upper M₂ : ℝ} (M : RealOutcomeModel d ε lower upper M₂)

def stencilLeadingEnergyKernel (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (θ : TensorIndex d p → ℝ) (X : StencilRole d p → d → ℝ) : ℝ :=
  (acceptedStencil p T x₀ h ℓ r).indicator (fun X => M.stencilTreatmentVariance p x₀ ℓ r X *
    tensorPolynomial p θ (observedAnchorCoordinate p x₀ h X) ^ 2) X

theorem stencilLeadingEnergyKernel_eq_sum (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (θ : TensorIndex d p → ℝ) (X : StencilRole d p → d → ℝ) :
    M.stencilLeadingEnergyKernel p T x₀ h ℓ r θ X =
      ∑ ν, ∑ ω, (θ ν * θ ω) * M.stencilLeadingKernel p T x₀ h ℓ r ν ω X := by
  by_cases hX : X ∈ acceptedStencil p T x₀ h ℓ r
  · simp only [stencilLeadingEnergyKernel, stencilLeadingKernel, Set.indicator_of_mem hX,
      tensorPolynomial, pow_two, Finset.sum_mul, Finset.mul_sum, stencilFeature, observedAnchorCoordinate]
    apply Finset.sum_congr rfl
    intro ν _
    apply Finset.sum_congr rfl
    intro ω _
    ring
  · simp only [stencilLeadingEnergyKernel, stencilLeadingKernel, Set.indicator_of_not_mem hX,
      mul_zero, Finset.sum_const_zero]

theorem stencilLeadingEnergyKernel_integrable (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (hε : 0 ≤ ε) (θ : TensorIndex d p → ℝ) :
    Integrable (M.stencilLeadingEnergyKernel p T x₀ h ℓ r θ)
      (Measure.pi (fun _ : StencilRole d p => M.design)) := by
  simp_rw [show M.stencilLeadingEnergyKernel p T x₀ h ℓ r θ =
    (fun X => ∑ ν, ∑ ω, (θ ν * θ ω) * M.stencilLeadingKernel p T x₀ h ℓ r ν ω X)
      from funext (M.stencilLeadingEnergyKernel_eq_sum p T x₀ h ℓ r θ)]
  exact integrable_finset_sum _ (fun ν _ => integrable_finset_sum _ (fun ω _ =>
    ((M.stencilLeadingKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh hε ν ω).integrable one_le_two).const_mul _))

theorem stencilLeadingGram_quadratic (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (hε : 0 ≤ ε) (θ : TensorIndex d p → ℝ) :
    (∑ ν, θ ν * (M.stencilLeadingGram p T x₀ h ℓ r *ᵥ θ) ν) =
      ∫ X, M.stencilLeadingEnergyKernel p T x₀ h ℓ r θ X
        ∂Measure.pi (fun _ : StencilRole d p => M.design) := by
  have hi (ν ω : TensorIndex d p) :=
    ((M.stencilLeadingKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh hε ν ω).integrable one_le_two).const_mul (θ ν * θ ω)
  simp_rw [M.stencilLeadingEnergyKernel_eq_sum p T x₀ h ℓ r θ]
  rw [integral_finset_sum _ (fun ν _ => integrable_finset_sum _ (fun ω _ => hi ν ω))]
  simp_rw [integral_finset_sum _ (fun ω _ => hi _ ω), integral_const_mul]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, stencilLeadingGram]
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem stencilLeadingGram_quadratic_lower (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hlower : 0 ≤ lower) (θ : TensorIndex d p → ℝ) :
    (ε * (1 - ε) * lower ^ Fintype.card (StencilRole d p) * (4 : ℝ) ^ Fintype.card d) *
      stencilMass p T h ℓ r * tensorGramEnergy p θ ≤
        ∑ ν, θ ν * (M.stencilLeadingGram p T x₀ h ℓ r *ᵥ θ) ν := by
  let F := (acceptedStencil p T x₀ h ℓ r).indicator
    (fun X => tensorPolynomial p θ (observedAnchorCoordinate p x₀ h X) ^ 2)
  have hF : Integrable F (Measure.pi (fun _ : StencilRole d p => M.design)) :=
    acceptedAnchorSquare_integrable p T x₀ h ℓ r θ _
  have hFnonneg : ∀ X, 0 ≤ F X := fun X => Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hden := integral_mono_measure (M.design_product_lower_domination (StencilRole d p))
    (Filter.Eventually.of_forall hFnonneg) hF
  rw [integral_smul_nnreal_measure] at hden
  have hsub := acceptedStencil_in_cube p T x₀ hx hh hhsmall hℓ hℓr hrh
  have hv : (∫ X, F X ∂volume.restrict (Set.univ.pi (fun _ : StencilRole d p => Icc (0 : d → ℝ) 1))) =
      (4 : ℝ) ^ Fintype.card d * stencilMass p T h ℓ r * tensorGramEnergy p θ := by
    dsimp only [F]
    rw [integral_indicator (acceptedStencil_measurable p T x₀ h ℓ r),
      Measure.restrict_restrict (acceptedStencil_measurable p T x₀ h ℓ r), Set.inter_eq_left.mpr hsub]
    exact acceptedStencil_anchor_energy p T x₀ hh hℓ (hℓ.trans_le hℓr) θ
  rw [hv] at hden
  simp only [NNReal.smul_def, NNReal.coe_pow, Real.coe_toNNReal _ hlower, smul_eq_mul] at hden
  rw [M.stencilLeadingGram_quadratic p T x₀ hx hh hhsmall hℓ hℓr hrh hε θ]
  calc
    _ = (ε * (1 - ε)) * (lower ^ Fintype.card (StencilRole d p) *
        ((4 : ℝ) ^ Fintype.card d * stencilMass p T h ℓ r * tensorGramEnergy p θ)) := by ring
    _ ≤ (ε * (1 - ε)) * ∫ X, F X ∂Measure.pi (fun _ : StencilRole d p => M.design) :=
      mul_le_mul_of_nonneg_left hden (mul_nonneg hε (sub_nonneg.mpr hε1))
    _ ≤ _ := by
      rw [← integral_const_mul]
      apply integral_mono_ae (hF.const_mul _)
        (M.stencilLeadingEnergyKernel_integrable p T x₀ hx hh hhsmall hℓ hℓr hrh hε θ)
      filter_upwards [M.stencilTreatmentVariance_bounds p x₀ ℓ r hε] with X hc
      by_cases hX : X ∈ acceptedStencil p T x₀ h ℓ r
      · simp only [F, stencilLeadingEnergyKernel, Set.indicator_of_mem hX]
        exact mul_le_mul_of_nonneg_right hc.2.2 (sq_nonneg _)
      · simp only [F, stencilLeadingEnergyKernel, Set.indicator_of_not_mem hX, mul_zero, le_refl]

end RealOutcomeModel
end CausalLowerbound.UpperBound

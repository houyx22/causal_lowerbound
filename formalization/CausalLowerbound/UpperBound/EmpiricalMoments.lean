import CausalLowerbound.UpperBound.FiniteStatisticMoments
import CausalLowerbound.UpperBound.PopulationResidual

/-! Vector and operator second moments of the concrete statistics.  All
integrability premises are derived from the real-outcome model. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

theorem splitTupleAverage_memLp {I Z : Type*} [Fintype I] [MeasurableSpace Z]
    {J : I → Type*} [∀ i, Fintype (J i)]
    (μ : Measure Z) [IsProbabilityMeasure μ] {K : (I → Z) → ℝ}
    (hK : MemLp K 2 (Measure.pi (fun _ : I => μ))) :
    MemLp (tupleAverage (fun a : ∀ i, J i => K ∘ tupleObservation a)) 2
      (Measure.pi (fun _ : Σ i, J i => μ)) :=
  (memLp_finset_sum _ (fun a _ => hK.comp_measurePreserving
    (tupleObservation_measurePreserving μ a))).const_mul _

namespace RealOutcomeModel

variable {d : Type*} [Fintype d] {ε lower upper M₂ : ℝ}
variable (M : RealOutcomeModel d ε lower upper M₂)

theorem empiricalStencilResponse_coordinate_memLp (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] (ν : TensorIndex d p) :
    MemLp (fun z => empiricalStencilResponse p T x₀ h ℓ r J z ν) 2
      (Measure.pi (fun _ : Σ i, J i => M.observationLaw)) := by
  have hk := M.stencilResponseKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh ν
  unfold empiricalStencilResponse tupleAverage
  exact (memLp_finset_sum _ (fun a _ => hk.comp_measurePreserving
    (tupleObservation_measurePreserving M.observationLaw a))).const_mul _

theorem empiricalStencilMatrix_coordinate_memLp (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] (ν ω : TensorIndex d p) :
    MemLp (fun z => empiricalStencilMatrix p T x₀ h ℓ r J z ν ω) 2
      (Measure.pi (fun _ : Σ i, J i => M.observationLaw)) := by
  have hk := M.stencilMatrixKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh ν ω
  unfold empiricalStencilMatrix tupleAverage
  exact (memLp_finset_sum _ (fun a _ => hk.comp_measurePreserving
    (tupleObservation_measurePreserving M.observationLaw a))).const_mul _

theorem empiricalStencilResponse_centered_norm_memLp (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] :
    MemLp (fun z => ‖empiricalStencilResponse p T x₀ h ℓ r J z - M.stencilPopulationResponse p T x₀ h ℓ r‖) 2
      (Measure.pi (fun _ : Σ i, J i => M.observationLaw)) :=
  memLp_pi_norm _ _ ((empiricalStencilResponse_measurable p T x₀ h ℓ r J).sub measurable_const)
    (fun ν => (M.empiricalStencilResponse_coordinate_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh J ν).sub (memLp_const _))

theorem empiricalStencilMatrix_centered_norm_memLp (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] :
    MemLp (fun z => ‖matrixOperator (empiricalStencilMatrix p T x₀ h ℓ r J z) -
      matrixOperator (M.stencilPopulationMatrix p T x₀ h ℓ r)‖) 2
      (Measure.pi (fun _ : Σ i, J i => M.observationLaw)) := by
  simp_rw [← matrixOperator_sub]
  exact memLp_matrixOperator_norm _ _
    (matrix_sub_const_measurable _ (empiricalStencilMatrix_measurable p T x₀ h ℓ r J) _)
    (fun ν ω => (M.empiricalStencilMatrix_coordinate_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh J ν ω).sub (memLp_const _))

theorem empiricalStencilResponse_meanSquare_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)] [∀ i, Nonempty (J i)]
    {η B : ℝ} (hU : 0 ≤ upper) (hη : 0 ≤ η) (hB : 1 ≤ B)
    (hUB : upper ≤ B) (hηC : η ≤ B * (coarseCellVolume p T r).toReal)
    (hJ : ∀ i, (Fintype.card (J i) : ℝ)⁻¹ ≤ η) :
    (∫ z, ‖empiricalStencilResponse p T x₀ h ℓ r J z - M.stencilPopulationResponse p T x₀ h ℓ r‖ ^ 2
      ∂Measure.pi (fun _ : Σ i, J i => M.observationLaw)) ≤
      (Fintype.card (TensorIndex d p) * ((2 : ℝ) ^ Fintype.card (StencilRole d p) *
        B ^ Fintype.card (StencilRole d p) *
        (2 * M₂ * (Fintype.card (StencilRole d p) : ℝ) ^ 2 * upper ^ Fintype.card (StencilRole d p)))) *
        stencilMass p T h ℓ r ^ 2 *
        (η / (h / 4) ^ Fintype.card d + η ^ 2 / ((h / 4) ^ Fintype.card d * ℓ ^ Fintype.card d)) := by
  apply (vector_centered_meanSquare_le_variances _ _
    (empiricalStencilResponse_measurable p T x₀ h ℓ r J)
    (M.empiricalStencilResponse_coordinate_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh J)
    (M.stencilPopulationResponse p T x₀ h ℓ r)
    (M.empiricalStencilResponse_mean p T x₀ hx hh hhsmall hℓ hℓr hrh J)).trans
  have he := Finset.sum_le_sum (fun ν (_ : ν ∈ Finset.univ) =>
    M.empiricalStencilResponse_variance_le p T x₀ hx hh hhsmall hℓ hℓr hrh J hU hη hB hUB hηC hJ ν)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using he

theorem empiricalStencilMatrix_meanSquare_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)] [∀ i, Nonempty (J i)]
    {η B : ℝ} (hU : 0 ≤ upper) (hη : 0 ≤ η) (hB : 1 ≤ B)
    (hUB : upper ≤ B) (hηC : η ≤ B * (coarseCellVolume p T r).toReal)
    (hJ : ∀ i, (Fintype.card (J i) : ℝ)⁻¹ ≤ η) :
    (∫ z, ‖matrixOperator (empiricalStencilMatrix p T x₀ h ℓ r J z) -
        matrixOperator (M.stencilPopulationMatrix p T x₀ h ℓ r)‖ ^ 2
      ∂Measure.pi (fun _ : Σ i, J i => M.observationLaw)) ≤
      ((Fintype.card (TensorIndex d p) : ℝ) ^ 4 * ((2 : ℝ) ^ Fintype.card (StencilRole d p) *
        B ^ Fintype.card (StencilRole d p) *
        ((Fintype.card (StencilRole d p) : ℝ) ^ 2 * upper ^ Fintype.card (StencilRole d p)))) *
        stencilMass p T h ℓ r ^ 2 *
        (η / (h / 4) ^ Fintype.card d + η ^ 2 / ((h / 4) ^ Fintype.card d * ℓ ^ Fintype.card d)) := by
  apply (matrix_centered_meanSquare_le_variances _ _
    (empiricalStencilMatrix_measurable p T x₀ h ℓ r J)
    (M.empiricalStencilMatrix_coordinate_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh J)
    (M.stencilPopulationMatrix p T x₀ h ℓ r)
    (M.empiricalStencilMatrix_mean p T x₀ hx hh hhsmall hℓ hℓr hrh J)).trans
  have he := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun ν (_ : ν ∈ Finset.univ) => Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) =>
      M.empiricalStencilMatrix_variance_le p T x₀ hx hh hhsmall hℓ hℓr hrh J hU hη hB hUB hηC hJ ν ω)))
    (sq_nonneg (Fintype.card (TensorIndex d p) : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at he
  convert he using 1 <;> ring

end RealOutcomeModel
end CausalLowerbound.UpperBound

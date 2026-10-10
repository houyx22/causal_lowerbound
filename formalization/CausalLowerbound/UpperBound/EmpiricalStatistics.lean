import CausalLowerbound.UpperBound.KernelVariance

/-! The actual vector and nonsymmetric matrix statistics formed from the
independent role groups.  Their coordinates are measurable, and the concrete
kernel bounds give the two-term variance estimate without moment assumptions
on these statistics as additional inputs. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {I Z : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Z]
variable {J : I → Type*} [∀ i, Fintype (J i)]

theorem tupleObservation_measurable (a : ∀ i, J i) : Measurable (tupleObservation (Z := Z) a) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply (⟨i, a i⟩ : Σ i, J i))

theorem tupleAverage_measurable {Ω : Type*} [MeasurableSpace Ω]
    (f : (∀ i, J i) → Ω → ℝ) (hf : ∀ a, Measurable (f a)) : Measurable (tupleAverage f) :=
  measurable_const.mul (Finset.measurable_sum Finset.univ (fun a _ => hf a))

theorem integral_splitSample (μ : Measure Z) [IsProbabilityMeasure μ] [∀ i, Nonempty (J i)]
    {K : (I → Z) → ℝ} (hK : Integrable K (Measure.pi (fun _ : I => μ))) :
    (∫ z, tupleAverage (fun a : ∀ i, J i => K ∘ tupleObservation a) z
      ∂Measure.pi (fun _ : Σ i, J i => μ)) = ∫ z, K z ∂Measure.pi (fun _ : I => μ) := by
  have hi (a : ∀ i, J i) : Integrable (K ∘ tupleObservation a)
      (Measure.pi (fun _ : Σ i, J i => μ)) :=
    ((tupleObservation_measurePreserving μ a).integrable_comp hK.aestronglyMeasurable).mpr hK
  have he (a : ∀ i, J i) : (∫ z, (K ∘ tupleObservation a) z ∂Measure.pi (fun _ : Σ i, J i => μ)) =
      ∫ z, K z ∂Measure.pi (fun _ : I => μ) :=
    integral_comp_measurePreserving (tupleObservation_measurePreserving μ a) hK.aestronglyMeasurable
  unfold tupleAverage
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun a _ => hi a)]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (∀ i, J i) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos (α := ∀ i, J i)))
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

variable {d : Type*} [Fintype d]

def empiricalStencilResponse (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)]
    (z : (Σ i, J i) → (d → ℝ) × (Bool × ℝ)) : TensorIndex d p → ℝ :=
  fun ν => tupleAverage (fun a => stencilResponseKernel p T x₀ h ℓ r ν ∘ tupleObservation a) z

def empiricalStencilMatrix (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)]
    (z : (Σ i, J i) → (d → ℝ) × (Bool × ℝ)) : Matrix (TensorIndex d p) (TensorIndex d p) ℝ :=
  fun ν ω => tupleAverage (fun a => stencilMatrixKernel p T x₀ h ℓ r ν ω ∘ tupleObservation a) z

theorem empiricalStencilResponse_measurable (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] :
    Measurable (empiricalStencilResponse p T x₀ h ℓ r J) := by
  apply measurable_pi_lambda
  intro ν
  exact tupleAverage_measurable _ (fun a =>
    (stencilResponseKernel_measurable p T x₀ h ℓ r ν).comp (tupleObservation_measurable a))

theorem empiricalStencilMatrix_measurable (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] :
    Measurable (empiricalStencilMatrix p T x₀ h ℓ r J) := by
  apply measurable_pi_lambda
  intro ν
  apply measurable_pi_lambda
  intro ω
  exact tupleAverage_measurable _ (fun a =>
    (stencilMatrixKernel_measurable p T x₀ h ℓ r ν ω).comp (tupleObservation_measurable a))

namespace RealOutcomeModel

variable {ε lower upper M₂ : ℝ} (M : RealOutcomeModel d ε lower upper M₂)

theorem empiricalStencilResponse_variance_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)] [∀ i, Nonempty (J i)]
    {η B : ℝ} (hU : 0 ≤ upper) (hη : 0 ≤ η) (hB : 1 ≤ B)
    (hUB : upper ≤ B) (hηC : η ≤ B * (coarseCellVolume p T r).toReal)
    (hJ : ∀ i, (Fintype.card (J i) : ℝ)⁻¹ ≤ η) (ν : TensorIndex d p) :
    variance (Measure.pi (fun _ : Σ i, J i => M.observationLaw))
        (fun z => empiricalStencilResponse p T x₀ h ℓ r J z ν) ≤
      ((2 : ℝ) ^ Fintype.card (StencilRole d p) * B ^ Fintype.card (StencilRole d p) *
        (2 * M₂ * (Fintype.card (StencilRole d p) : ℝ) ^ 2 * upper ^ Fintype.card (StencilRole d p))) *
        stencilMass p T h ℓ r ^ 2 *
        (η / (h / 4) ^ Fintype.card d + η ^ 2 / ((h / 4) ^ Fintype.card d * ℓ ^ Fintype.card d)) := by
  exact M.stencil_variance_le_mass p T x₀ hh hℓ (hℓ.trans_le hℓr) J
    (M.stencilResponseKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh ν)
    (stencilResponseKernel_off p T x₀ h ℓ r ν) hU hη hB hUB hηC hJ
    (M.stencilResponseKernel_secondMoment_le_mass p T x₀ hx hh hhsmall hℓ hℓr hrh hU ν)

theorem empiricalStencilMatrix_variance_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)] [∀ i, Nonempty (J i)]
    {η B : ℝ} (hU : 0 ≤ upper) (hη : 0 ≤ η) (hB : 1 ≤ B)
    (hUB : upper ≤ B) (hηC : η ≤ B * (coarseCellVolume p T r).toReal)
    (hJ : ∀ i, (Fintype.card (J i) : ℝ)⁻¹ ≤ η) (ν ω : TensorIndex d p) :
    variance (Measure.pi (fun _ : Σ i, J i => M.observationLaw))
        (fun z => empiricalStencilMatrix p T x₀ h ℓ r J z ν ω) ≤
      ((2 : ℝ) ^ Fintype.card (StencilRole d p) * B ^ Fintype.card (StencilRole d p) *
        ((Fintype.card (StencilRole d p) : ℝ) ^ 2 * upper ^ Fintype.card (StencilRole d p))) *
        stencilMass p T h ℓ r ^ 2 *
        (η / (h / 4) ^ Fintype.card d + η ^ 2 / ((h / 4) ^ Fintype.card d * ℓ ^ Fintype.card d)) := by
  exact M.stencil_variance_le_mass p T x₀ hh hℓ (hℓ.trans_le hℓr) J
    (M.stencilMatrixKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh ν ω)
    (stencilMatrixKernel_off p T x₀ h ℓ r ν ω) hU hη hB hUB hηC hJ
    (M.stencilMatrixKernel_secondMoment_le_mass p T x₀ hx hh hhsmall hℓ hℓr hrh hU ν ω)

end RealOutcomeModel
end CausalLowerbound.UpperBound

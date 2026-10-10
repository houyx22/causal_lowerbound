import CausalLowerbound.UpperBound.ObservedFeatures
import CausalLowerbound.UpperBound.CompletionProbability
import CausalLowerbound.UpperBound.ConditionalScoreMoment
import CausalLowerbound.UpperBound.RealOutcomeMoments

/-! The concrete vector and nonsymmetric matrix kernels in the local estimating
equation.  Both are set to zero outside the measured stencil event.  Their
L² properties use a second moment of Y and bounded binary treatment only. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]

theorem residualScore_measurable_comp (w t : Ω → I → ℝ) (z : Ω → I → Bool × ℝ)
    (hw : Measurable w) (ht : Measurable t) (hz : Measurable z) :
    Measurable (fun x => residualScore (w x) (t x) (z x)) := by
  have hA (i : I) : Measurable (fun x => treatmentValue (z x i)) :=
    measurable_treatmentValue.comp ((measurable_pi_apply i).comp hz)
  have hY (i : I) : Measurable (fun x => (z x i).2) :=
    ((measurable_pi_apply i).comp hz).snd
  unfold residualScore coordinateContrast
  exact (Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp hw).mul (hA i))).mul
    (Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp hw).mul
      ((hY i).sub (((measurable_pi_apply i).comp ht).mul (hA i)))))

variable {d : Type*} [Fintype d]

def stencilResponseKernel (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (ν : TensorIndex d p) (z : StencilRole d p → (d → ℝ) × (Bool × ℝ)) : ℝ :=
  if z ∈ acceptedObservationStencil p T x₀ h ℓ r then
    stencilFeatureMean p x₀ h ℓ r (fun i => (z i).1) ν *
      residualScore (observedStencilWeights p x₀ ℓ r (fun i => (z i).1)) 0 (fun i => (z i).2)
  else 0

def stencilMatrixKernel (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (ν ω : TensorIndex d p) (z : StencilRole d p → (d → ℝ) × (Bool × ℝ)) : ℝ :=
  if z ∈ acceptedObservationStencil p T x₀ h ℓ r then
    stencilFeatureMean p x₀ h ℓ r (fun i => (z i).1) ν *
      (∑ i, observedStencilWeights p x₀ ℓ r (fun i => (z i).1) i * treatmentValue (z i).2) *
      (∑ i, observedStencilWeights p x₀ ℓ r (fun i => (z i).1) i * treatmentValue (z i).2 *
        stencilFeature p x₀ h (fun i => (z i).1) i ω)
  else 0

theorem stencilResponseKernel_off (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ)
    (h ℓ r : ℝ) (ν : TensorIndex d p) (z : StencilRole d p → (d → ℝ) × (Bool × ℝ))
    (hz : z ∉ acceptedObservationStencil p T x₀ h ℓ r) :
    stencilResponseKernel p T x₀ h ℓ r ν z = 0 := if_neg hz

theorem stencilMatrixKernel_off (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ)
    (h ℓ r : ℝ) (ν ω : TensorIndex d p) (z : StencilRole d p → (d → ℝ) × (Bool × ℝ))
    (hz : z ∉ acceptedObservationStencil p T x₀ h ℓ r) :
    stencilMatrixKernel p T x₀ h ℓ r ν ω z = 0 := if_neg hz

theorem stencilResponseKernel_measurable (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (ν : TensorIndex d p) :
    Measurable (stencilResponseKernel p T x₀ h ℓ r ν) := by
  have hX : Measurable (fun z : StencilRole d p → (d → ℝ) × (Bool × ℝ) => fun i => (z i).1) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply i).fst)
  have hZ : Measurable (fun z : StencilRole d p → (d → ℝ) × (Bool × ℝ) => fun i => (z i).2) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply i).snd)
  have hw := (observedStencilWeights_measurable p x₀ ℓ r).comp hX
  have hm := (stencilFeatureMean_measurable p x₀ h ℓ r ν).comp hX
  exact Measurable.ite (acceptedObservationStencil_measurable p T x₀ h ℓ r)
    (hm.mul (residualScore_measurable_comp _ _ _ hw measurable_const hZ)) measurable_const

theorem stencilMatrixKernel_measurable (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (ν ω : TensorIndex d p) :
    Measurable (stencilMatrixKernel p T x₀ h ℓ r ν ω) := by
  have hX : Measurable (fun z : StencilRole d p → (d → ℝ) × (Bool × ℝ) => fun i => (z i).1) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply i).fst)
  have hw := (observedStencilWeights_measurable p x₀ ℓ r).comp hX
  have hm := (stencilFeatureMean_measurable p x₀ h ℓ r ν).comp hX
  have hA (i : StencilRole d p) :=
    ((measurable_pi_apply i).comp hw).mul (measurable_treatmentValue.comp (measurable_pi_apply i).snd)
  have hC := Finset.measurable_sum Finset.univ (fun i _ => hA i)
  have hD := Finset.measurable_sum Finset.univ (fun i _ => (hA i).mul
    ((stencilFeature_continuous p x₀ h i ω).measurable.comp hX))
  have hprod := (hm.mul hC).mul hD
  exact Measurable.ite (acceptedObservationStencil_measurable p T x₀ h ℓ r) hprod measurable_const

theorem stencilResponseKernel_sq_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (ν : TensorIndex d p) (z : StencilRole d p → (d → ℝ) × (Bool × ℝ)) :
    stencilResponseKernel p T x₀ h ℓ r ν z ^ 2 ≤
      Fintype.card (StencilRole d p) * ∑ i, (z i).2.2 ^ 2 := by
  by_cases hz : z ∈ acceptedObservationStencil p T x₀ h ℓ r
  · rw [stencilResponseKernel, if_pos hz, mul_pow]
    have hm := stencilFeatureMean_bound p x₀ h ℓ r (fun i => (z i).1) ν
      (fun i => acceptedStencil_feature_bound p T x₀ hx hh hhsmall hℓ hℓr hrh _ hz i ν)
    have hm₂ : stencilFeatureMean p x₀ h ℓ r (fun i => (z i).1) ν ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr hm
    calc
      _ ≤ residualScore (observedStencilWeights p x₀ ℓ r (fun i => (z i).1)) 0
          (fun i => (z i).2) ^ 2 := mul_le_of_le_one_left (sq_nonneg _) hm₂
      _ ≤ _ := by
        simpa only [Pi.zero_apply, zero_mul, sub_zero] using
          residualScore_sq_le (observedStencilWeights p x₀ ℓ r (fun i => (z i).1)) 0
            (observedStencilWeights_norm_sq p x₀ ℓ r _) (fun i => (z i).2)
  · rw [stencilResponseKernel_off p T x₀ h ℓ r ν z hz, zero_pow (by decide : 2 ≠ 0)]
    positivity

theorem stencilMatrixKernel_sq_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (ν ω : TensorIndex d p) (z : StencilRole d p → (d → ℝ) × (Bool × ℝ)) :
    stencilMatrixKernel p T x₀ h ℓ r ν ω z ^ 2 ≤ (Fintype.card (StencilRole d p) : ℝ) ^ 2 := by
  by_cases hz : z ∈ acceptedObservationStencil p T x₀ h ℓ r
  · let X := fun i => (z i).1
    let w := observedStencilWeights p x₀ ℓ r X
    have hw : ∑ i, w i ^ 2 = 1 := observedStencilWeights_norm_sq p x₀ ℓ r X
    have hφ (i : StencilRole d p) (a : TensorIndex d p) : |stencilFeature p x₀ h X i a| ≤ 1 :=
      acceptedStencil_feature_bound p T x₀ hx hh hhsmall hℓ hℓr hrh X hz i a
    have hm₂ : stencilFeatureMean p x₀ h ℓ r X ν ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr (stencilFeatureMean_bound p x₀ h ℓ r X ν (fun i => hφ i ν))
    have hA := treatmentContrast_sq_le w hw (fun i => (z i).2)
    have hAφ : (∑ i, w i * treatmentValue (z i).2 * stencilFeature p x₀ h X i ω) ^ 2 ≤
        Fintype.card (StencilRole d p) := by
      have hb (i : StencilRole d p) :
          (treatmentValue (z i).2 * stencilFeature p x₀ h X i ω) ^ 2 ≤ 1 := by
        apply (sq_le_one_iff_abs_le_one _).mpr
        rw [abs_mul]
        exact mul_le_one₀ (by simpa only [Real.norm_eq_abs] using treatmentValue_bound (z i).2)
          (abs_nonneg _) (hφ i ω)
      calc
        _ = coordinateContrast w (fun i u => treatmentValue u * stencilFeature p x₀ h X i ω)
            (fun i => (z i).2) ^ 2 := by simp only [coordinateContrast, mul_assoc]
        _ ≤ ∑ i, (treatmentValue (z i).2 * stencilFeature p x₀ h X i ω) ^ 2 :=
          coordinateContrast_sq_le w _ hw _
        _ ≤ ∑ _i : StencilRole d p, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hb i)
        _ = Fintype.card (StencilRole d p) := by simp
    rw [stencilMatrixKernel, if_pos hz, mul_pow, mul_pow]
    have he := mul_le_mul (mul_le_mul hm₂ hA (sq_nonneg _) zero_le_one) hAφ
      (sq_nonneg _) (by positivity : 0 ≤ (1 : ℝ) * Fintype.card (StencilRole d p))
    simpa only [one_mul, pow_two, coordinateContrast, X, w] using he
  · rw [stencilMatrixKernel_off p T x₀ h ℓ r ν ω z hz, zero_pow (by decide : 2 ≠ 0)]
    positivity

namespace RealOutcomeModel

variable {ε lower upper M₂ : ℝ} (M : RealOutcomeModel d ε lower upper M₂)

theorem stencilResponseKernel_memLp (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (ν : TensorIndex d p) :
    MemLp (stencilResponseKernel p T x₀ h ℓ r ν) 2 (M.sampleLaw (StencilRole d p)) := by
  have hm : AEStronglyMeasurable (stencilResponseKernel p T x₀ h ℓ r ν)
      (M.sampleLaw (StencilRole d p)) :=
    (stencilResponseKernel_measurable p T x₀ h ℓ r ν).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  have hY (i : StencilRole d p) : Integrable
      (fun z : StencilRole d p → (d → ℝ) × (Bool × ℝ) => (z i).2.2 ^ 2)
      (M.sampleLaw (StencilRole d p)) :=
    (M.observation_response_memLp.comp_measurePreserving
      (coordinate_eval_measurePreserving (fun _ : StencilRole d p => M.observationLaw) i)).integrable_sq
  apply ((integrable_finset_sum Finset.univ (fun i _ => hY i)).const_mul
    (Fintype.card (StencilRole d p) : ℝ)).mono' (hm.pow 2)
  exact Filter.Eventually.of_forall (fun z => by
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq] using
      stencilResponseKernel_sq_le p T x₀ hx hh hhsmall hℓ hℓr hrh ν z)

theorem stencilMatrixKernel_memLp (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (ν ω : TensorIndex d p) :
    MemLp (stencilMatrixKernel p T x₀ h ℓ r ν ω) 2 (M.sampleLaw (StencilRole d p)) := by
  have hm : AEStronglyMeasurable (stencilMatrixKernel p T x₀ h ℓ r ν ω)
      (M.sampleLaw (StencilRole d p)) :=
    (stencilMatrixKernel_measurable p T x₀ h ℓ r ν ω).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (integrable_const ((Fintype.card (StencilRole d p) : ℝ) ^ 2)).mono' (hm.pow 2)
  exact Filter.Eventually.of_forall (fun z => by
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq] using
      stencilMatrixKernel_sq_le p T x₀ hx hh hhsmall hℓ hℓr hrh ν ω z)

end RealOutcomeModel
end CausalLowerbound.UpperBound

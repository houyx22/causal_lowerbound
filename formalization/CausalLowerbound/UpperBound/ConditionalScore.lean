import CausalLowerbound.UpperBound.IndependentCoordinates
import CausalLowerbound.UpperBound.RealOutcomeMoments
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The conditional score identity for binary treatment and real outcomes.
All weights and Taylor values may depend on the entire covariate tuple.
The identities hold simultaneously for all such values outside one null set. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {I Z : Type*} [Fintype I] [MeasurableSpace Z]

def coordinateContrast (w : I → ℝ) (f : I → Z → ℝ) (z : I → Z) : ℝ :=
  ∑ i, w i * f i (z i)

theorem coordinateContrast_memLp (μ : I → Measure Z)
    [∀ i, IsProbabilityMeasure (μ i)] (w : I → ℝ) (f : I → Z → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    MemLp (coordinateContrast w f) 2 (Measure.pi μ) :=
  memLp_finset_sum _ (fun i _ =>
    ((hf i).comp_measurePreserving (coordinate_eval_measurePreserving μ i)).const_mul (w i))

theorem integral_coordinateContrast (μ : I → Measure Z)
    [∀ i, IsProbabilityMeasure (μ i)] (w : I → ℝ) (f : I → Z → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    (∫ z, coordinateContrast w f z ∂Measure.pi μ) = ∑ i, w i * ∫ z, f i z ∂μ i := by
  unfold coordinateContrast
  rw [integral_finset_sum Finset.univ (f := fun (i : I) (z : I → Z) => w i * f i (z i)) (fun i _ =>
    (((hf i).comp_measurePreserving (coordinate_eval_measurePreserving μ i)).integrable
      one_le_two).const_mul (w i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_coordinate μ i (hf i).aestronglyMeasurable]

theorem covariance_coordinateContrasts (μ : I → Measure Z)
    [∀ i, IsProbabilityMeasure (μ i)] (w v : I → ℝ) (f g : I → Z → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) (hg : ∀ i, MemLp (g i) 2 (μ i)) :
    covariance (Measure.pi μ) (coordinateContrast w f) (coordinateContrast v g) =
      ∑ i, w i * v i * covariance (μ i) (f i) (g i) := by
  unfold coordinateContrast
  rw [covariance_sum_sum (Measure.pi μ) (fun i z => w i * f i (z i))
    (fun i z => v i * g i (z i))
    (fun i => ((hf i).comp_measurePreserving
      (coordinate_eval_measurePreserving μ i)).const_mul (w i))
    (fun i => ((hg i).comp_measurePreserving
      (coordinate_eval_measurePreserving μ i)).const_mul (v i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_same_coordinate μ i (hf i) (hg i)]
    ring
  · intro j _ hji
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_distinct_coordinates μ i j hji.symm (hf i) (hg j), mul_zero, mul_zero]
  · simp

omit [MeasurableSpace Z] in
theorem coordinateContrast_sq_le (w : I → ℝ) (f : I → Z → ℝ)
    (hw : ∑ i, w i ^ 2 = 1) (z : I → Z) :
    coordinateContrast w f z ^ 2 ≤ ∑ i, f i (z i) ^ 2 := by
  simpa only [coordinateContrast, hw, one_mul] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w (fun i => f i (z i))

namespace RealOutcomeModel

variable {d : Type*} [Fintype d] {ε lower upper M₂ : ℝ}
variable (M : RealOutcomeModel d ε lower upper M₂)

def conditionalTupleLaw (X : I → d → ℝ) : Measure (I → Bool × ℝ) :=
  Measure.pi (fun i => M.conditional (X i))

instance conditionalTupleLaw_probability (X : I → d → ℝ) :
    IsProbabilityMeasure (M.conditionalTupleLaw X) := by
  unfold conditionalTupleLaw
  infer_instance

theorem conditional_score_identity :
    ∀ᵐ X ∂Measure.pi (fun _ : I => M.design), ∀ w t : I → ℝ,
      (∫ z, coordinateContrast w (fun _ => treatmentValue) z *
          coordinateContrast w (fun i z => z.2 - t i * treatmentValue z) z
        ∂M.conditionalTupleLaw X) =
        (∑ i, w i * M.propensity (X i)) *
          (∑ i, w i * (M.baseline (X i) +
            M.propensity (X i) * (M.effect (X i) - t i))) +
        ∑ i, w i ^ 2 * M.propensity (X i) * (1 - M.propensity (X i)) *
          (M.effect (X i) - t i) := by
  have hgood := M.response_memLp.and (M.treatment_mean.and
    (M.conditional_residual_mean_all.and M.conditional_residual_covariance_all))
  have htuple : ∀ᵐ X ∂Measure.pi (fun _ : I => M.design), ∀ i,
      MemLp (fun z : Bool × ℝ => z.2) 2 (M.conditional (X i)) ∧
      (∫ z, treatmentValue z ∂M.conditional (X i)) = M.propensity (X i) ∧
      (∀ t : ℝ, (∫ z, z.2 - t * treatmentValue z ∂M.conditional (X i)) =
        M.baseline (X i) + M.propensity (X i) * (M.effect (X i) - t)) ∧
      (∀ t : ℝ, covariance (M.conditional (X i)) treatmentValue
        (fun z => z.2 - t * treatmentValue z) =
        M.propensity (X i) * (1 - M.propensity (X i)) * (M.effect (X i) - t)) :=
    ae_all_iff.mpr (fun i =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : I => M.design) (i := i)).eventually hgood)
  filter_upwards [htuple] with X hX
  intro w t
  let μ := fun i => M.conditional (X i)
  have hA (i : I) : MemLp treatmentValue 2 (μ i) := treatmentValue_memLp _
  have hR (i : I) : MemLp (fun z => z.2 - t i * treatmentValue z) 2 (μ i) :=
    (hX i).1.sub ((hA i).const_mul (t i))
  have hc := covariance_coordinateContrasts μ w w
    (fun _ => treatmentValue) (fun i z => z.2 - t i * treatmentValue z) hA hR
  have hmA := integral_coordinateContrast μ w (fun _ => treatmentValue) hA
  have hmR := integral_coordinateContrast μ w
    (fun i z => z.2 - t i * treatmentValue z) hR
  simp only [μ, fun i => (hX i).2.1] at hmA
  simp only [μ, fun i => (hX i).2.2.1 (t i)] at hmR
  rw [covariance, hmA, hmR] at hc
  have hd : (∑ i, w i * w i * covariance (μ i) treatmentValue
      (fun z => z.2 - t i * treatmentValue z)) =
      ∑ i, w i ^ 2 * M.propensity (X i) * (1 - M.propensity (X i)) *
        (M.effect (X i) - t i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [(hX i).2.2.2 (t i)]
    ring
  rw [hd] at hc
  exact (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)

end RealOutcomeModel
end CausalLowerbound.UpperBound

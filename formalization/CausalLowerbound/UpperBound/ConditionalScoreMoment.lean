import CausalLowerbound.UpperBound.ConditionalScore

/-! Second moments of the conditional score use bounded treatment, not
bounded response.  No product of two unbounded responses occurs in a kernel. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {I : Type*} [Fintype I]

def residualScore (w t : I → ℝ) (z : I → Bool × ℝ) : ℝ :=
  coordinateContrast w (fun _ => treatmentValue) z *
    coordinateContrast w (fun i z => z.2 - t i * treatmentValue z) z

theorem treatmentContrast_sq_le (w : I → ℝ) (hw : ∑ i, w i ^ 2 = 1)
    (z : I → Bool × ℝ) :
    coordinateContrast w (fun _ => treatmentValue) z ^ 2 ≤ Fintype.card I := by
  apply (coordinateContrast_sq_le w (fun _ => treatmentValue) hw z).trans
  calc
    (∑ i, treatmentValue (z i) ^ 2) ≤ ∑ _i : I, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      cases hz : z i with
      | mk a y => cases a <;> norm_num [treatmentValue]
    _ = Fintype.card I := by simp

theorem residualScore_sq_le (w t : I → ℝ) (hw : ∑ i, w i ^ 2 = 1)
    (z : I → Bool × ℝ) :
    residualScore w t z ^ 2 ≤
      Fintype.card I * ∑ i, ((z i).2 - t i * treatmentValue (z i)) ^ 2 := by
  rw [residualScore, mul_pow]
  exact mul_le_mul (treatmentContrast_sq_le w hw z)
    (coordinateContrast_sq_le w _ hw z) (sq_nonneg _) (Nat.cast_nonneg _)

theorem residualScore_memLp (μ : I → Measure (Bool × ℝ))
    [∀ i, IsProbabilityMeasure (μ i)] (w t : I → ℝ) (hw : ∑ i, w i ^ 2 = 1)
    (hY : ∀ i, MemLp (fun z : Bool × ℝ => z.2) 2 (μ i)) :
    MemLp (residualScore w t) 2 (Measure.pi μ) := by
  have hR (i : I) := (hY i).sub ((treatmentValue_memLp (μ i)).const_mul (t i))
  have hA := coordinateContrast_memLp μ w (fun _ => treatmentValue)
    (fun i => treatmentValue_memLp (μ i))
  have hRc := coordinateContrast_memLp μ w
    (fun i z => z.2 - t i * treatmentValue z) hR
  have hm : AEStronglyMeasurable (residualScore w t) (Measure.pi μ) :=
    hA.aestronglyMeasurable.mul hRc.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  have hi : Integrable (fun z : I → Bool × ℝ =>
      (Fintype.card I : ℝ) * ∑ i, ((z i).2 - t i * treatmentValue (z i)) ^ 2)
      (Measure.pi μ) :=
    (integrable_finset_sum Finset.univ (fun i _ =>
      ((hR i).comp_measurePreserving (coordinate_eval_measurePreserving μ i)).integrable_sq)).const_mul _
  apply hi.mono' (hm.pow 2)
  exact Filter.Eventually.of_forall (fun z => by
    simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_sq] using residualScore_sq_le w t hw z)

theorem residualScore_secondMoment_le (μ : I → Measure (Bool × ℝ))
    [∀ i, IsProbabilityMeasure (μ i)] (w t : I → ℝ) (hw : ∑ i, w i ^ 2 = 1)
    (hY : ∀ i, MemLp (fun z : Bool × ℝ => z.2) 2 (μ i)) :
    (∫ z, residualScore w t z ^ 2 ∂Measure.pi μ) ≤
      Fintype.card I * ∑ i, ∫ z, (z.2 - t i * treatmentValue z) ^ 2 ∂μ i := by
  have hR (i : I) := (hY i).sub ((treatmentValue_memLp (μ i)).const_mul (t i))
  have hi (i : I) :=
    ((hR i).comp_measurePreserving (coordinate_eval_measurePreserving μ i)).integrable_sq
  calc
    _ ≤ ∫ z : I → Bool × ℝ,
        (Fintype.card I : ℝ) * ∑ i, ((z i).2 - t i * treatmentValue (z i)) ^ 2 ∂Measure.pi μ :=
      integral_mono (residualScore_memLp μ w t hw hY).integrable_sq
        ((integrable_finset_sum Finset.univ (fun i _ => hi i)).const_mul _)
        (residualScore_sq_le w t hw)
    _ = _ := by
      rw [integral_const_mul, integral_finset_sum Finset.univ
        (f := fun (i : I) (z : I → Bool × ℝ) => ((z i).2 - t i * treatmentValue (z i)) ^ 2)
        (fun i _ => hi i)]
      congr 1
      exact Finset.sum_congr rfl (fun i _ =>
        integral_coordinate μ i (hR i).integrable_sq.aestronglyMeasurable)

namespace RealOutcomeModel

variable {d : Type*} [Fintype d] {ε lower upper M₂ : ℝ}
variable (M : RealOutcomeModel d ε lower upper M₂)

theorem conditional_score_secondMoment_le :
    ∀ᵐ X ∂Measure.pi (fun _ : I => M.design), ∀ w t : I → ℝ,
      (∑ i, w i ^ 2 = 1) →
      (∫ z, residualScore w t z ^ 2 ∂M.conditionalTupleLaw X) ≤
        Fintype.card I * ∑ i, (2 * M₂ + 2 * t i ^ 2) := by
  have hgood := M.response_memLp.and M.conditional_residual_second_moment_all
  have ht := ae_all_iff.mpr (fun i : I =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : I => M.design) (i := i)).eventually hgood)
  filter_upwards [ht] with X hX
  intro w t hw
  exact (residualScore_secondMoment_le (fun i => M.conditional (X i)) w t hw
    (fun i => (hX i).1)).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hX i).2 (t i)))
      (Nat.cast_nonneg _))

end RealOutcomeModel
end CausalLowerbound.UpperBound

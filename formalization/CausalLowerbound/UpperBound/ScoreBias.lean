import CausalLowerbound.UpperBound.ConditionalScoreMoment

/-! A deterministic bound for the conditional score.  The nuisance term is
the product of the two small contrasts; every Taylor-error term is bounded
by a fixed multiple of the maximum approximation error. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {I : Type*} [Fintype I]

theorem normalized_weight_abs_le_one (w : I → ℝ) (hw : ∑ i, w i ^ 2 = 1) (i : I) : |w i| ≤ 1 := by
  apply (sq_le_one_iff_abs_le_one _).mp
  calc
    _ ≤ ∑ j, w j ^ 2 := Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
    _ = 1 := hw

theorem normalized_weights_abs_sum_le_card (w : I → ℝ) (hw : ∑ i, w i ^ 2 = 1) :
    (∑ i, |w i|) ≤ Fintype.card I := by
  calc
    _ ≤ ∑ _i : I, (1 : ℝ) := Finset.sum_le_sum (fun i _ => normalized_weight_abs_le_one w hw i)
    _ = _ := by simp

theorem weighted_sum_abs_le (w v : I → ℝ) {W R : ℝ} (hR : 0 ≤ R)
    (hw : (∑ i, |w i|) ≤ W) (hv : ∀ i, |v i| ≤ R) : |∑ i, w i * v i| ≤ W * R := by
  calc
    _ ≤ ∑ i, |w i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |w i| * R := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _))
    _ = (∑ i, |w i|) * R := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hw hR

def scorePopulationValue (w π μ e : I → ℝ) : ℝ :=
  (∑ i, w i * π i) * (∑ i, w i * (μ i + π i * e i)) +
    ∑ i, w i ^ 2 * π i * (1 - π i) * e i

theorem scorePopulationValue_bound (w π μ e : I → ℝ) (hw : ∑ i, w i ^ 2 = 1)
    (hπ : ∀ i, 0 ≤ π i ∧ π i ≤ 1) {A B R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hπc : |∑ i, w i * π i| ≤ A) (hμc : |∑ i, w i * μ i| ≤ B)
    (he : ∀ i, |e i| ≤ R) :
    |scorePopulationValue w π μ e| ≤ A * B + ((Fintype.card I : ℝ) ^ 2 + 1) * R := by
  have hπabs (i : I) : |π i| ≤ 1 := by rw [abs_of_nonneg (hπ i).1]; exact (hπ i).2
  have hπc' : |∑ i, w i * π i| ≤ Fintype.card I := by
    simpa only [mul_one] using weighted_sum_abs_le w π zero_le_one
      (normalized_weights_abs_sum_le_card w hw) hπabs
  have hπe : |∑ i, w i * (π i * e i)| ≤ Fintype.card I * R :=
    weighted_sum_abs_le w (fun i => π i * e i) hR (normalized_weights_abs_sum_le_card w hw)
      (fun i => by
        rw [abs_mul]
        exact (mul_le_mul (hπabs i) (he i) (abs_nonneg _) zero_le_one).trans_eq (one_mul R))
  have hd : |∑ i, w i ^ 2 * π i * (1 - π i) * e i| ≤ R := by
    have hv (i : I) : |π i * (1 - π i) * e i| ≤ R := by
      have hcomp : |1 - π i| ≤ 1 := by rw [abs_of_nonneg (by linarith [(hπ i).2])]; linarith [(hπ i).1]
      rw [abs_mul, abs_mul]
      exact (mul_le_mul (mul_le_one₀ (hπabs i) (abs_nonneg _) hcomp)
        (he i) (abs_nonneg _) zero_le_one).trans_eq (one_mul R)
    have hb := weighted_sum_abs_le (fun i => w i ^ 2) (fun i => π i * (1 - π i) * e i) hR
      (show (∑ i, |w i ^ 2|) ≤ 1 by simp only [abs_sq, hw, le_refl]) hv
    simpa only [one_mul, mul_assoc] using hb
  have hexp : scorePopulationValue w π μ e =
      (∑ i, w i * π i) * (∑ i, w i * μ i) +
        (∑ i, w i * π i) * (∑ i, w i * (π i * e i)) +
          ∑ i, w i ^ 2 * π i * (1 - π i) * e i := by
    simp only [scorePopulationValue, mul_add, Finset.sum_add_distrib]
  rw [hexp]
  calc
    _ ≤ |(∑ i, w i * π i) * (∑ i, w i * μ i)| +
        |(∑ i, w i * π i) * (∑ i, w i * (π i * e i))| +
        |∑ i, w i ^ 2 * π i * (1 - π i) * e i| :=
      (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ A * B + (Fintype.card I : ℝ) * (Fintype.card I * R) + R := by
      gcongr
      · rw [abs_mul]
        exact mul_le_mul hπc hμc (abs_nonneg _) hA
      · rw [abs_mul]
        exact mul_le_mul hπc' hπe (abs_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by ring

namespace RealOutcomeModel

variable {d : Type*} [Fintype d] {ε lower upper M₂ : ℝ} (M : RealOutcomeModel d ε lower upper M₂)

theorem conditional_residualScore_identity :
    ∀ᵐ X ∂Measure.pi (fun _ : I => M.design), ∀ w t : I → ℝ,
      (∫ z, residualScore w t z ∂M.conditionalTupleLaw X) =
        scorePopulationValue w (fun i => M.propensity (X i)) (fun i => M.baseline (X i))
          (fun i => M.effect (X i) - t i) :=
  M.conditional_score_identity

theorem tuple_propensity_mem_unit (hε : 0 ≤ ε) :
    ∀ᵐ X ∂Measure.pi (fun _ : I => M.design), ∀ i, 0 ≤ M.propensity (X i) ∧ M.propensity (X i) ≤ 1 := by
  have hg : ∀ᵐ x ∂M.design, 0 ≤ M.propensity x ∧ M.propensity x ≤ 1 :=
    M.overlap.mono (fun x hx => ⟨hε.trans hx.1, hx.2.trans (sub_le_self 1 hε)⟩)
  exact ae_all_iff.mpr (fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : I => M.design) (i := i)).eventually hg)

end RealOutcomeModel
end CausalLowerbound.UpperBound

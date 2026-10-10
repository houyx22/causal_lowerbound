import CausalLowerbound.UpperBound.ConditionalMatrix
import CausalLowerbound.UpperBound.FeatureVariation

/-! A pointwise comparison between the conditional estimating matrix and
its positive anchor Gram term.  Only bounded binary propensities, normalized
weights and the proved feature variation are needed. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {I : Type*} [Fintype I]

def weightedTreatmentVariance (w π : I → ℝ) : ℝ := ∑ i, w i ^ 2 * π i * (1 - π i)

theorem binary_variance_mem_unit {π : ℝ} (hπ : 0 ≤ π ∧ π ≤ 1) :
    0 ≤ π * (1 - π) ∧ π * (1 - π) ≤ 1 := by
  constructor
  · exact mul_nonneg hπ.1 (sub_nonneg.mpr hπ.2)
  · nlinarith [sq_nonneg π]

theorem binary_variance_overlap_lower {ε π : ℝ} (hπ : ε ≤ π ∧ π ≤ 1 - ε) :
    ε * (1 - ε) ≤ π * (1 - π) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hπ.1) (sub_nonneg.mpr hπ.2)]

theorem weightedTreatmentVariance_mem_unit (w π : I → ℝ)
    (hw : ∑ i, w i ^ 2 = 1) (hπ : ∀ i, 0 ≤ π i ∧ π i ≤ 1) :
    0 ≤ weightedTreatmentVariance w π ∧ weightedTreatmentVariance w π ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun i _ => by
      rw [mul_assoc]
      exact mul_nonneg (sq_nonneg _) (binary_variance_mem_unit (hπ i)).1)
  · calc
      _ ≤ ∑ i, w i ^ 2 := Finset.sum_le_sum (fun i _ => by
        rw [mul_assoc]
        exact mul_le_of_le_one_right (sq_nonneg _) (binary_variance_mem_unit (hπ i)).2)
      _ = 1 := hw

theorem weightedTreatmentVariance_lower (w π : I → ℝ)
    (hw : ∑ i, w i ^ 2 = 1) {ε : ℝ} (hπ : ∀ i, ε ≤ π i ∧ π i ≤ 1 - ε) :
    ε * (1 - ε) ≤ weightedTreatmentVariance w π := by
  calc
    _ = ∑ i, w i ^ 2 * (ε * (1 - ε)) := by rw [← Finset.sum_mul, hw, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (binary_variance_overlap_lower (hπ i)) (sq_nonneg _))

theorem squared_weight_mean_abs_le_one (w φ : I → ℝ)
    (hw : ∑ i, w i ^ 2 = 1) (hφ : ∀ i, |φ i| ≤ 1) :
    |∑ i, w i ^ 2 * φ i| ≤ 1 := by
  calc
    _ ≤ ∑ i, |w i ^ 2 * φ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i ^ 2 := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul, abs_sq]
      exact mul_le_of_le_one_right (sq_nonneg _) (hφ i))
    _ = 1 := hw

theorem variance_feature_abs_le_one (w π φ : I → ℝ)
    (hw : ∑ i, w i ^ 2 = 1) (hπ : ∀ i, 0 ≤ π i ∧ π i ≤ 1)
    (hφ : ∀ i, |φ i| ≤ 1) :
    |∑ i, w i ^ 2 * π i * (1 - π i) * φ i| ≤ 1 := by
  have he : (∑ i, w i ^ 2 * π i * (1 - π i) * φ i) =
      ∑ i, w i ^ 2 * (π i * (1 - π i) * φ i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  apply squared_weight_mean_abs_le_one w _ hw
  intro i
  rw [abs_mul, abs_of_nonneg (binary_variance_mem_unit (hπ i)).1]
  exact mul_le_one₀ (binary_variance_mem_unit (hπ i)).2 (abs_nonneg _) (hφ i)

theorem matrixPopulationValue_abs_le (w π φ : I → ℝ)
    (hw : ∑ i, w i ^ 2 = 1) (hπ : ∀ i, 0 ≤ π i ∧ π i ≤ 1)
    (hφ : ∀ i, |φ i| ≤ 1) :
    |matrixPopulationValue w π φ| ≤ (Fintype.card I : ℝ) ^ 2 + 1 := by
  have hs : |∑ i, w i * π i| ≤ Fintype.card I := by
    simpa only [mul_one] using weighted_sum_abs_le w π zero_le_one
      (normalized_weights_abs_sum_le_card w hw) (fun i => by rw [abs_of_nonneg (hπ i).1]; exact (hπ i).2)
  have ht : |∑ i, w i * π i * φ i| ≤ Fintype.card I := by
    have he := weighted_sum_abs_le w (fun i => π i * φ i) zero_le_one
      (normalized_weights_abs_sum_le_card w hw) (fun i => by
        rw [abs_mul, abs_of_nonneg (hπ i).1]
        exact mul_le_one₀ (hπ i).2 (abs_nonneg _) (hφ i))
    simpa only [mul_assoc, mul_one] using he
  unfold matrixPopulationValue
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  simpa only [pow_two] using add_le_add
    (mul_le_mul hs ht (abs_nonneg _) (Nat.cast_nonneg _))
    (variance_feature_abs_le_one w π φ hw hπ hφ)

theorem propensity_feature_contrast_bound (w π φ : I → ℝ) (a : ℝ) {A V : ℝ}
    (hπ : ∀ i, 0 ≤ π i ∧ π i ≤ 1) (ha : |a| ≤ 1)
    (hA : |∑ i, w i * π i| ≤ A) (hV : (∑ i, |w i| * |φ i - a|) ≤ V) :
    |∑ i, w i * π i * φ i| ≤ A + V := by
  have he : (∑ i, w i * π i * φ i) =
      (∑ i, w i * π i) * a + ∑ i, w i * π i * (φ i - a) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) ha).trans hA
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply le_trans _ hV
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul, abs_mul, abs_of_nonneg (hπ i).1]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (abs_nonneg _) (hπ i).2) (abs_nonneg _)

theorem variance_feature_difference_bound (w π φ : I → ℝ) (a : ℝ) {V : ℝ}
    (hw : ∑ i, w i ^ 2 = 1) (hπ : ∀ i, 0 ≤ π i ∧ π i ≤ 1)
    (hV : (∑ i, |w i| * |φ i - a|) ≤ V) :
    |(∑ i, w i ^ 2 * π i * (1 - π i) * φ i) - weightedTreatmentVariance w π * a| ≤ V := by
  have he : (∑ i, w i ^ 2 * π i * (1 - π i) * φ i) - weightedTreatmentVariance w π * a =
      ∑ i, w i ^ 2 * (π i * (1 - π i)) * (φ i - a) := by
    simp only [weightedTreatmentVariance, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  calc
    _ ≤ ∑ i, |w i ^ 2 * (π i * (1 - π i)) * (φ i - a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, w i ^ 2 * |φ i - a| := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul, abs_mul, abs_sq, abs_of_nonneg (binary_variance_mem_unit (hπ i)).1]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (sq_nonneg _) (binary_variance_mem_unit (hπ i)).2) (abs_nonneg _))
    _ ≤ _ := (squared_weight_variation_le w φ a hw).trans hV

theorem matrixPopulationValue_anchor_comparison (w π u φ : I → ℝ) (a b : ℝ) {A V : ℝ}
    (hw : ∑ i, w i ^ 2 = 1) (hπ : ∀ i, 0 ≤ π i ∧ π i ≤ 1)
    (hu : ∀ i, |u i| ≤ 1) (hφ : ∀ i, |φ i| ≤ 1) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hA : 0 ≤ A) (hV : 0 ≤ V) (hcontrast : |∑ i, w i * π i| ≤ A)
    (huvar : (∑ i, |w i| * |u i - a|) ≤ V)
    (hφvar : (∑ i, |w i| * |φ i - b|) ≤ V) :
    |(∑ i, w i ^ 2 * u i) * matrixPopulationValue w π φ -
      weightedTreatmentVariance w π * a * b| ≤ A * (A + V) + 2 * V := by
  let m := ∑ i, w i ^ 2 * u i
  let s := ∑ i, w i * π i
  let t := ∑ i, w i * π i * φ i
  let v := ∑ i, w i ^ 2 * π i * (1 - π i) * φ i
  have hm : |m| ≤ 1 := squared_weight_mean_abs_le_one w u hw hu
  have hmd : |m - a| ≤ V := (squared_weight_mean_difference w u a hw).trans huvar
  have ht : |t| ≤ A + V := propensity_feature_contrast_bound w π φ b hπ hb hcontrast hφvar
  have hv : |v| ≤ 1 := variance_feature_abs_le_one w π φ hw hπ hφ
  have hvd : |v - weightedTreatmentVariance w π * b| ≤ V :=
    variance_feature_difference_bound w π φ b hw hπ hφvar
  change |m * (s * t + v) - weightedTreatmentVariance w π * a * b| ≤ _
  have he : m * (s * t + v) - weightedTreatmentVariance w π * a * b =
      m * (s * t) + (m - a) * v + a * (v - weightedTreatmentVariance w π * b) := by ring
  rw [he]
  calc
    _ ≤ |m * (s * t)| + |(m - a) * v| + |a * (v - weightedTreatmentVariance w π * b)| :=
      (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ A * (A + V) + V + V := by
      simp only [abs_mul]
      apply add_le_add
      · apply add_le_add
        · exact (mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hm).trans
            (mul_le_mul hcontrast ht (abs_nonneg _) hA)
        · exact (mul_le_of_le_one_right (abs_nonneg _) hv).trans hmd
      · exact (mul_le_of_le_one_left (abs_nonneg _) ha).trans hvd
    _ = _ := by ring

end CausalLowerbound.UpperBound

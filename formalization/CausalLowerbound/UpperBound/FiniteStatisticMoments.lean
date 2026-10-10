import CausalLowerbound.UpperBound.MeasurableEstimator
import CausalLowerbound.UpperBound.Covariance

/-! Passing from finitely many coordinate moments to vector and matrix
operator moments.  The bounds retain the sum of coordinate variances. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

variable {I J Ω : Type*} [Fintype I] [Fintype J] [MeasurableSpace Ω]

theorem pi_norm_le_sum_abs (x : I → ℝ) : ‖x‖ ≤ ∑ i, |x i| := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mpr
  intro i
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)

theorem pi_norm_sq_le_sum_sq (x : I → ℝ) : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
  have hs : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : ‖x‖ ≤ Real.sqrt (∑ i, x i ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    simpa only [Real.norm_eq_abs, sq_abs] using
      (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (x j)) (Finset.mem_univ i))
  exact ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hb).trans_eq (Real.sq_sqrt hs)

theorem matrixOperator_norm_le_sum_abs (A : Matrix I J ℝ) :
    ‖matrixOperator A‖ ≤ Fintype.card J * ∑ i, ∑ j, |A i j| := by
  apply matrixOperator_norm_le_entries A
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
  intro i j
  exact (Finset.single_le_sum (fun k _ => abs_nonneg (A i k)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (A k l))) (Finset.mem_univ i))

theorem matrixOperator_norm_sq_le_sum_sq (A : Matrix I J ℝ) :
    ‖matrixOperator A‖ ^ 2 ≤ (Fintype.card J : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2 := by
  have hs : 0 ≤ ∑ i, ∑ j, A i j ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have he (i : I) (j : J) : |A i j| ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    exact (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i))
  have hb := (sq_le_sq₀ (norm_nonneg (matrixOperator A)) (by positivity)).mpr
    (matrixOperator_norm_le_entries A (Real.sqrt_nonneg _) he)
  simpa only [mul_pow, Real.sq_sqrt hs] using hb

theorem memLp_pi_norm (μ : Measure Ω) (f : Ω → I → ℝ) (hf : Measurable f)
    (hc : ∀ i, MemLp (fun z => f z i) 2 μ) : MemLp (fun z => ‖f z‖) 2 μ := by
  have hs := memLp_finset_sum Finset.univ (fun i _ => (hc i).norm)
  apply hs.mono' hf.aestronglyMeasurable.norm
  apply Filter.Eventually.of_forall
  intro z
  simpa only [Real.norm_eq_abs, abs_norm] using pi_norm_le_sum_abs (f z)

theorem memLp_matrixOperator_norm (μ : Measure Ω) (f : Ω → Matrix I J ℝ) (hf : Measurable f)
    (hc : ∀ i j, MemLp (fun z => f z i j) 2 μ) :
    MemLp (fun z => ‖matrixOperator (f z)‖) 2 μ := by
  have hs := (memLp_finset_sum Finset.univ (fun i _ =>
    memLp_finset_sum Finset.univ (fun j _ => (hc i j).norm))).const_mul (Fintype.card J : ℝ)
  apply hs.mono' (matrixOperator_continuous.measurable.comp hf).aestronglyMeasurable.norm
  apply Filter.Eventually.of_forall
  intro z
  simpa only [Real.norm_eq_abs, abs_norm] using matrixOperator_norm_le_sum_abs (f z)

theorem matrix_sub_const_measurable (f : Ω → Matrix I J ℝ) (hf : Measurable f) (m : Matrix I J ℝ) :
    Measurable (fun z => f z - m) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (((measurable_pi_apply j).comp (measurable_pi_apply i)).comp hf).sub measurable_const

theorem vector_centered_meanSquare_le_variances (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → I → ℝ) (hf : Measurable f) (hc : ∀ i, MemLp (fun z => f z i) 2 μ)
    (m : I → ℝ) (hm : ∀ i, (∫ z, f z i ∂μ) = m i) :
    (∫ z, ‖f z - m‖ ^ 2 ∂μ) ≤ ∑ i, variance μ (fun z => f z i) := by
  have hd (i : I) : MemLp (fun z => f z i - m i) 2 μ := (hc i).sub (memLp_const _)
  have hn := memLp_pi_norm μ (fun z => f z - m) (hf.sub measurable_const) hd
  calc
    _ ≤ ∫ z, ∑ i, (f z i - m i) ^ 2 ∂μ := integral_mono hn.integrable_sq
      (integrable_finset_sum _ (fun i _ => (hd i).integrable_sq)) (fun z => pi_norm_sq_le_sum_sq (f z - m))
    _ = ∑ i, ∫ z, (f z i - m i) ^ 2 ∂μ := integral_finset_sum _ (fun i _ => (hd i).integrable_sq)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [variance, covariance_eq_centered (hc i) (hc i), hm i]
      simp only [pow_two]

theorem matrix_centered_meanSquare_le_variances (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → Matrix I J ℝ) (hf : Measurable f) (hc : ∀ i j, MemLp (fun z => f z i j) 2 μ)
    (m : Matrix I J ℝ) (hm : ∀ i j, (∫ z, f z i j ∂μ) = m i j) :
    (∫ z, ‖matrixOperator (f z) - matrixOperator m‖ ^ 2 ∂μ) ≤
      (Fintype.card J : ℝ) ^ 2 * ∑ i, ∑ j, variance μ (fun z => f z i j) := by
  have hd (i : I) (j : J) : MemLp (fun z => f z i j - m i j) 2 μ := (hc i j).sub (memLp_const _)
  have hn := memLp_matrixOperator_norm μ (fun z => f z - m) (matrix_sub_const_measurable f hf m) hd
  have hs := integrable_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => (hd i j).integrable_sq))
  simp_rw [← matrixOperator_sub]
  calc
    _ ≤ ∫ z, (Fintype.card J : ℝ) ^ 2 * ∑ i, ∑ j, (f z i j - m i j) ^ 2 ∂μ :=
      integral_mono hn.integrable_sq (hs.const_mul _) (fun z => matrixOperator_norm_sq_le_sum_sq (f z - m))
    _ = (Fintype.card J : ℝ) ^ 2 * ∑ i, ∑ j, ∫ z, (f z i j - m i j) ^ 2 ∂μ := by
      rw [integral_const_mul, integral_finset_sum _ (fun i _ =>
        integrable_finset_sum _ (fun j _ => (hd i j).integrable_sq))]
      simp_rw [integral_finset_sum _ (fun j _ => (hd _ j).integrable_sq)]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [variance, covariance_eq_centered (hc i j) (hc i j), hm i j]
      simp only [pow_two]

end CausalLowerbound.UpperBound

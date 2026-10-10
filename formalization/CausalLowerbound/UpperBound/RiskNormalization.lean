import CausalLowerbound.UpperBound.RiskReduction

/-! Cancel the acceptance-mass normalization in the clipped estimator's
mean squared error.  This step separates fixed constants from bandwidths. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory

namespace CausalLowerbound.UpperBound

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace Ω]

theorem clippedEstimate_normalized_mse_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c q L bias V Cb CQ : ℝ} (hc : 0 < c) (hq : 0 < q) (hL : 0 ≤ L)
    (hbias : 0 ≤ bias) (hV : 0 ≤ V) (hCb : 0 ≤ Cb) (hCQ : 0 ≤ CQ)
    (η : E →L[ℝ] ℝ) (hη : ‖η‖ ≤ 1) (Q : E →L[ℝ] E) (b θ : E) (hθ : ‖θ‖ ≤ L)
    (Qhat : Ω → E →L[ℝ] E) (bhat : Ω → E)
    (hQ : ∀ x, (2 * (c * q)) * ‖x‖ ≤ ‖Q x‖)
    (hest : AEStronglyMeasurable
      (fun z => clippedEstimate (c * q) (mul_pos hc hq) L η (Qhat z) (bhat z)) μ)
    (hb : MemLp (fun z => ‖bhat z - b‖) 2 μ)
    (hm : MemLp (fun z => ‖Qhat z - Q‖) 2 μ)
    (hbm : (∫ z, ‖bhat z - b‖ ^ 2 ∂μ) ≤ Cb * q ^ 2 * V)
    (hmm : (∫ z, ‖Qhat z - Q‖ ^ 2 ∂μ) ≤ CQ * q ^ 2 * V)
    (hpop : ‖b - Q θ‖ ≤ bias * q) :
    (∫ z, (clippedEstimate (c * q) (mul_pos hc hq) L η (Qhat z) (bhat z) - η θ) ^ 2 ∂μ) ≤
      3 / c ^ 2 * (bias ^ 2 + (Cb + 9 * L ^ 2 * CQ) * V) := by
  have hκ := mul_pos hc hq
  have hηθ : |η θ| ≤ L := (η.le_opNorm θ).trans
    ((mul_le_of_le_one_left (norm_nonneg _) hη).trans hθ)
  have hτ : -L ≤ η θ ∧ η θ ≤ L := abs_le.mp hηθ
  have he := clippedEstimate_mse_bound μ hκ hL η Q b θ Qhat bhat hQ hτ hest hb hm
  have he₁ : (‖η‖ / (c * q)) ^ 2 ≤ (1 / (c * q)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (div_le_div_of_nonneg_right hη hκ.le)
  have he₂ : ((‖η‖ * ‖θ‖ + 2 * L) / (c * q)) ^ 2 ≤ (3 * L / (c * q)) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    apply div_le_div_of_nonneg_right _ hκ.le
    have hh := (mul_le_of_le_one_left (norm_nonneg θ) hη).trans hθ
    linarith
  have he₃ : ‖b - Q θ‖ ^ 2 ≤ (bias * q) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hbias hq.le)).mpr hpop
  apply he.trans
  calc
    _ ≤ 3 * ((1 / (c * q)) ^ 2 * (Cb * q ^ 2 * V) +
        (1 / (c * q)) ^ 2 * (bias * q) ^ 2 +
        (3 * L / (c * q)) ^ 2 * (CQ * q ^ 2 * V)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add
      · exact add_le_add
          (mul_le_mul he₁ hbm (integral_nonneg (fun z => sq_nonneg _)) (sq_nonneg _))
          (mul_le_mul he₁ he₃ (sq_nonneg _) (sq_nonneg _))
      · exact mul_le_mul he₂ hmm (integral_nonneg (fun z => sq_nonneg _)) (sq_nonneg _)
    _ = _ := by field_simp; ring

end CausalLowerbound.UpperBound

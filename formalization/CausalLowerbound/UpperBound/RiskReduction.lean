import CausalLowerbound.UpperBound.StableInverse
import CausalLowerbound.UpperBound.Covariance

/-! Reduce the mean squared error of the clipped, truncated inverse to the
two empirical second moments and the population bias.  This is a deterministic
perturbation argument followed by integration; it needs no fourth moments. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory

namespace CausalLowerbound.UpperBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def clippedEstimate (κ : ℝ) (hκ : 0 < κ) (L : ℝ) (η : E →L[ℝ] ℝ)
    (T : E →L[ℝ] E) (b : E) : ℝ := clip L (η (truncatedSolve κ hκ T b))

theorem clippedEstimate_error_bound {κ L : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L)
    (η : E →L[ℝ] ℝ) (Q Qhat : E →L[ℝ] E) (b bhat θ : E)
    (hQ : ∀ x, (2 * κ) * ‖x‖ ≤ ‖Q x‖) (hτ : -L ≤ η θ ∧ η θ ≤ L) :
    |clippedEstimate κ hκ L η Qhat bhat - η θ| ≤
      (‖η‖ / κ) * (‖bhat - b‖ + ‖b - Q θ‖) +
        ((‖η‖ * ‖θ‖ + 2 * L) / κ) * ‖Qhat - Q‖ := by
  by_cases hgood : ‖Qhat - Q‖ ≤ κ
  · have hp : |η (truncatedSolve κ hκ Qhat bhat) - η θ| ≤
        ‖η‖ * ‖truncatedSolve κ hκ Qhat bhat - θ‖ := by
      simpa only [map_sub, Real.norm_eq_abs] using
        η.le_opNorm (truncatedSolve κ hκ Qhat bhat - θ)
    have hb := (abs_clip_sub_le hτ (η (truncatedSolve κ hκ Qhat bhat))).trans
      (hp.trans (mul_le_mul_of_nonneg_left
        (truncatedSolve_error_on_good_event hκ Q Qhat b bhat θ hQ hgood) (norm_nonneg η)))
    change |clippedEstimate κ hκ L η Qhat bhat - η θ| ≤ _ at hb
    have he : ‖η‖ * ((‖bhat - b‖ + ‖b - Q θ‖ + ‖Qhat - Q‖ * ‖θ‖) / κ) =
        (‖η‖ / κ) * (‖bhat - b‖ + ‖b - Q θ‖) +
          (‖η‖ * ‖θ‖ / κ) * ‖Qhat - Q‖ := by ring
    rw [he] at hb
    have hz : 0 ≤ (2 * L / κ) * ‖Qhat - Q‖ := by positivity
    calc
      _ ≤ (‖η‖ / κ) * (‖bhat - b‖ + ‖b - Q θ‖) +
          (‖η‖ * ‖θ‖ / κ) * ‖Qhat - Q‖ := hb
      _ ≤ ((‖η‖ / κ) * (‖bhat - b‖ + ‖b - Q θ‖) +
          (‖η‖ * ‖θ‖ / κ) * ‖Qhat - Q‖) + (2 * L / κ) * ‖Qhat - Q‖ :=
        le_add_of_nonneg_right hz
      _ = _ := by ring
  · have hb := abs_clip_sub_le_twice hL hτ (η (truncatedSolve κ hκ Qhat bhat))
    change |clippedEstimate κ hκ L η Qhat bhat - η θ| ≤ 2 * L at hb
    have hlarge : κ ≤ ‖Qhat - Q‖ := le_of_lt (lt_of_not_ge hgood)
    have hh : 2 * L ≤ (2 * L / κ) * ‖Qhat - Q‖ := by
      calc
        2 * L = (2 * L / κ) * κ := (div_mul_cancel₀ _ hκ.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hlarge (by positivity)
    have hrest : 0 ≤ (‖η‖ / κ) * (‖bhat - b‖ + ‖b - Q θ‖) +
        (‖η‖ * ‖θ‖ / κ) * ‖Qhat - Q‖ := by positivity
    calc
      _ ≤ (2 * L / κ) * ‖Qhat - Q‖ := hb.trans hh
      _ ≤ (2 * L / κ) * ‖Qhat - Q‖ +
          ((‖η‖ / κ) * (‖bhat - b‖ + ‖b - Q θ‖) +
            (‖η‖ * ‖θ‖ / κ) * ‖Qhat - Q‖) := le_add_of_nonneg_right hrest
      _ = _ := by ring

theorem clippedEstimate_squared_error_bound {κ L : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L)
    (η : E →L[ℝ] ℝ) (Q Qhat : E →L[ℝ] E) (b bhat θ : E)
    (hQ : ∀ x, (2 * κ) * ‖x‖ ≤ ‖Q x‖) (hτ : -L ≤ η θ ∧ η θ ≤ L) :
    (clippedEstimate κ hκ L η Qhat bhat - η θ) ^ 2 ≤
      3 * ((‖η‖ / κ) ^ 2 * ‖bhat - b‖ ^ 2 +
        (‖η‖ / κ) ^ 2 * ‖b - Q θ‖ ^ 2 +
        ((‖η‖ * ‖θ‖ + 2 * L) / κ) ^ 2 * ‖Qhat - Q‖ ^ 2) := by
  have hb := clippedEstimate_error_bound hκ hL η Q Qhat b bhat θ hQ hτ
  have hs := sq_le_sq₀ (abs_nonneg (clippedEstimate κ hκ L η Qhat bhat - η θ)) (show 0 ≤
    (‖η‖ / κ) * (‖bhat - b‖ + ‖b - Q θ‖) +
      ((‖η‖ * ‖θ‖ + 2 * L) / κ) * ‖Qhat - Q‖ by positivity)
  have he := hs.mpr hb
  simp only [sq_abs] at he
  nlinarith [sq_nonneg ((‖η‖ / κ) * ‖bhat - b‖ - (‖η‖ / κ) * ‖b - Q θ‖),
    sq_nonneg ((‖η‖ / κ) * ‖bhat - b‖ -
      ((‖η‖ * ‖θ‖ + 2 * L) / κ) * ‖Qhat - Q‖),
    sq_nonneg ((‖η‖ / κ) * ‖b - Q θ‖ -
      ((‖η‖ * ‖θ‖ + 2 * L) / κ) * ‖Qhat - Q‖)]

/-- The measurability of the constructed estimator is an explicit hypothesis
here; the paper-specific sampling and matrix construction must establish it. -/
theorem clippedEstimate_mse_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {κ L : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L)
    (η : E →L[ℝ] ℝ) (Q : E →L[ℝ] E) (b θ : E)
    (Qhat : Ω → E →L[ℝ] E) (bhat : Ω → E)
    (hQ : ∀ x, (2 * κ) * ‖x‖ ≤ ‖Q x‖) (hτ : -L ≤ η θ ∧ η θ ≤ L)
    (hest : AEStronglyMeasurable (fun ω => clippedEstimate κ hκ L η (Qhat ω) (bhat ω)) μ)
    (hb : MemLp (fun ω => ‖bhat ω - b‖) 2 μ)
    (hmat : MemLp (fun ω => ‖Qhat ω - Q‖) 2 μ) :
    (∫ ω, (clippedEstimate κ hκ L η (Qhat ω) (bhat ω) - η θ) ^ 2 ∂μ) ≤
      3 * ((‖η‖ / κ) ^ 2 * (∫ ω, ‖bhat ω - b‖ ^ 2 ∂μ) +
        (‖η‖ / κ) ^ 2 * ‖b - Q θ‖ ^ 2 +
        ((‖η‖ * ‖θ‖ + 2 * L) / κ) ^ 2 * (∫ ω, ‖Qhat ω - Q‖ ^ 2 ∂μ)) := by
  have herr : MemLp (fun ω => clippedEstimate κ hκ L η (Qhat ω) (bhat ω) - η θ) 2 μ :=
    MemLp.of_bound (hest.sub aestronglyMeasurable_const) (2 * L)
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, clippedEstimate] using
          abs_clip_sub_le_twice hL hτ (η (truncatedSolve κ hκ (Qhat ω) (bhat ω))))
  have h₁ := hb.integrable_sq.const_mul ((‖η‖ / κ) ^ 2)
  have h₂ : Integrable (fun _ : Ω => (‖η‖ / κ) ^ 2 * ‖b - Q θ‖ ^ 2) μ := integrable_const _
  have h₃ := hmat.integrable_sq.const_mul (((‖η‖ * ‖θ‖ + 2 * L) / κ) ^ 2)
  have hi := integral_mono herr.integrable_sq (((h₁.add h₂).add h₃).const_mul 3)
    (fun ω => clippedEstimate_squared_error_bound hκ hL η Q (Qhat ω) b (bhat ω) θ hQ hτ)
  have hsum : (∫ ω, (((‖η‖ / κ) ^ 2 * ‖bhat ω - b‖ ^ 2 +
        (‖η‖ / κ) ^ 2 * ‖b - Q θ‖ ^ 2) +
        ((‖η‖ * ‖θ‖ + 2 * L) / κ) ^ 2 * ‖Qhat ω - Q‖ ^ 2) ∂μ) =
      (‖η‖ / κ) ^ 2 * (∫ ω, ‖bhat ω - b‖ ^ 2 ∂μ) +
        (‖η‖ / κ) ^ 2 * ‖b - Q θ‖ ^ 2 +
        ((‖η‖ * ‖θ‖ + 2 * L) / κ) ^ 2 * (∫ ω, ‖Qhat ω - Q‖ ^ 2 ∂μ) := by
    rw [integral_add (f := fun ω => (‖η‖ / κ) ^ 2 * ‖bhat ω - b‖ ^ 2 +
        (‖η‖ / κ) ^ 2 * ‖b - Q θ‖ ^ 2) (h₁.add h₂) h₃,
      integral_add (f := fun ω => (‖η‖ / κ) ^ 2 * ‖bhat ω - b‖ ^ 2) h₁ h₂]
    simp only [integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul]
  simpa only [Pi.add_apply, integral_const_mul, hsum] using hi

end CausalLowerbound.UpperBound

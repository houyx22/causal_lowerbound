import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Deterministic stability of the truncated inverse.  No symmetry is
assumed: the empirical Gram operator in the two-scale estimator is generally
not self-adjoint. -/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace CausalLowerbound.UpperBound

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem lower_bound_add_perturbation (T R : E →L[ℝ] F) (c e : ℝ)
    (hT : ∀ x, c * ‖x‖ ≤ ‖T x‖) (hR : ‖R‖ ≤ e) (x : E) :
    (c - e) * ‖x‖ ≤ ‖(T + R) x‖ := by
  have hr : ‖R x‖ ≤ e * ‖x‖ :=
    (R.le_opNorm x).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg x))
  have ht : ‖T x‖ ≤ ‖T x + R x‖ + ‖R x‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (T x + R x) (R x)
  change (c - e) * ‖x‖ ≤ ‖T x + R x‖
  nlinarith [hT x]

theorem lower_bound_injective (T : E →L[ℝ] F) {c : ℝ} (hc : 0 < c)
    (hT : ∀ x, c * ‖x‖ ≤ ‖T x‖) : Function.Injective T := by
  intro x y hxy
  have hz : T (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hb := hT (x - y)
  rw [hz, norm_zero] at hb
  have hn : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

variable [FiniteDimensional ℝ E]

/-- Invert if the operator has the requested lower norm bound; return zero
otherwise.  In finite dimension the lower bound proves invertibility. -/
def truncatedSolve (κ : ℝ) (hκ : 0 < κ) (T : E →L[ℝ] E) (b : E) : E :=
  if h : ∀ x, κ * ‖x‖ ≤ ‖T x‖ then
    (LinearEquiv.ofInjectiveEndo T.toLinearMap (lower_bound_injective T hκ h)).symm b
  else 0

theorem apply_truncatedSolve_of_lower_bound {κ : ℝ} (hκ : 0 < κ)
    (T : E →L[ℝ] E) (b : E) (hT : ∀ x, κ * ‖x‖ ≤ ‖T x‖) :
    T (truncatedSolve κ hκ T b) = b := by
  rw [truncatedSolve, dif_pos hT]
  exact (LinearEquiv.ofInjectiveEndo T.toLinearMap (lower_bound_injective T hκ hT)).apply_symm_apply b

theorem truncatedSolve_residual_bound {κ : ℝ} (hκ : 0 < κ)
    (T : E →L[ℝ] E) (b θ : E) (hT : ∀ x, κ * ‖x‖ ≤ ‖T x‖) :
    ‖truncatedSolve κ hκ T b - θ‖ ≤ ‖b - T θ‖ / κ := by
  apply (le_div_iff₀ hκ).mpr
  have hb := hT (truncatedSolve κ hκ T b - θ)
  rw [map_sub, apply_truncatedSolve_of_lower_bound hκ T b hT] at hb
  simpa only [mul_comm] using hb

theorem truncatedSolve_error_on_good_event {κ : ℝ} (hκ : 0 < κ)
    (Q Qhat : E →L[ℝ] E) (b bhat θ : E)
    (hQ : ∀ x, (2 * κ) * ‖x‖ ≤ ‖Q x‖) (hgood : ‖Qhat - Q‖ ≤ κ) :
    ‖truncatedSolve κ hκ Qhat bhat - θ‖ ≤
      (‖bhat - b‖ + ‖b - Q θ‖ + ‖Qhat - Q‖ * ‖θ‖) / κ := by
  have hQhat : ∀ x, κ * ‖x‖ ≤ ‖Qhat x‖ := by
    intro x
    have h := lower_bound_add_perturbation Q (Qhat - Q) (2 * κ) κ hQ hgood x
    have heq : Q + (Qhat - Q) = Qhat := by abel
    simpa only [heq, show 2 * κ - κ = κ by ring] using h
  have he : bhat - Qhat θ = (bhat - b) + (b - Q θ) - (Qhat - Q) θ := by
    simp only [ContinuousLinearMap.sub_apply]
    abel
  have hn : ‖bhat - Qhat θ‖ ≤ ‖bhat - b‖ + ‖b - Q θ‖ + ‖Qhat - Q‖ * ‖θ‖ := by
    rw [he]
    exact (norm_sub_le _ _).trans
      (add_le_add (norm_add_le _ _) ((Qhat - Q).le_opNorm θ))
  exact (truncatedSolve_residual_bound hκ Qhat bhat θ hQhat).trans
    (div_le_div_of_nonneg_right hn hκ.le)

def clip (L x : ℝ) : ℝ := max (-L) (min L x)

theorem clip_mem (L x : ℝ) (hL : 0 ≤ L) : -L ≤ clip L x ∧ clip L x ≤ L := by
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clip_eq_self {L x : ℝ} (hx : -L ≤ x ∧ x ≤ L) : clip L x = x := by
  rw [clip, min_eq_right hx.2, max_eq_right hx.1]

theorem abs_clip_sub_le {L τ : ℝ} (hτ : -L ≤ τ ∧ τ ≤ L) (x : ℝ) :
    |clip L x - τ| ≤ |x - τ| := by
  have hL : -L ≤ L := hτ.1.trans hτ.2
  by_cases hlo : x < -L
  · rw [clip, min_eq_right (hlo.le.trans hL), max_eq_left hlo.le,
      abs_of_nonpos (by linarith : -L - τ ≤ 0), abs_of_nonpos (by linarith : x - τ ≤ 0)]
    linarith
  · by_cases hhi : x ≤ L
    · rw [clip_eq_self ⟨le_of_not_gt hlo, hhi⟩]
    · rw [clip, min_eq_left (le_of_not_ge hhi), max_eq_right hL,
        abs_of_nonneg (by linarith : 0 ≤ L - τ), abs_of_nonneg (by linarith : 0 ≤ x - τ)]
      linarith

theorem abs_clip_sub_le_twice {L τ : ℝ} (hL : 0 ≤ L)
    (hτ : -L ≤ τ ∧ τ ≤ L) (x : ℝ) : |clip L x - τ| ≤ 2 * L := by
  obtain ⟨hlo, hhi⟩ := clip_mem L x hL
  apply abs_le.mpr
  constructor <;> linarith

end CausalLowerbound.UpperBound

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A quantitative Taylor bridge with exactly the available smoothness.
For a function of class C^(q,θ), the remainder after degree q depends on
the oscillation of the q-th derivative, not on a (q+1)-st derivative. -/

noncomputable section
set_option autoImplicit false
open Set

namespace CausalLowerbound.UpperBound

/-- Subtracting the highest Taylor coefficient from the degree-(q-1)
Lagrange formula only requires q continuous derivatives. -/
theorem taylor_remainder_eq_derivative_difference {f : ℝ → ℝ} {a b : ℝ}
    {n : ℕ} (hab : a < b) (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) :
    ∃ y ∈ Ioo a b,
      f b - taylorWithinEval f (n + 1) (Icc a b) a b =
        (iteratedDerivWithin (n + 1) f (Icc a b) y -
          iteratedDerivWithin (n + 1) f (Icc a b) a) *
          (b - a) ^ (n + 1) / (n + 1).factorial := by
  have hd := hf.differentiableOn_iteratedDerivWithin
    (m := n) (by exact_mod_cast Nat.lt_succ_self n) (uniqueDiffOn_Icc hab)
  obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange hab hf.of_succ
    (hd.mono Ioo_subset_Icc_self)
  refine ⟨y, hy, ?_⟩
  rw [taylorWithinEval_succ, sub_add_eq_sub_sub, he]
  simp only [smul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, div_eq_mul_inv]
  ring

/-- The Hölder remainder of order q+θ.  This includes integer smoothness
under the convention θ=1 and q one less than the integer order. -/
theorem holder_taylor_remainder_succ {f : ℝ → ℝ} {a b L θ : ℝ} {n : ℕ}
    (hab : a < b) (hL : 0 ≤ L) (hθ : 0 ≤ θ)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b))
    (hholder : ∀ y ∈ Icc a b,
      |iteratedDerivWithin (n + 1) f (Icc a b) y -
        iteratedDerivWithin (n + 1) f (Icc a b) a| ≤ L * |y - a| ^ θ) :
    |f b - taylorWithinEval f (n + 1) (Icc a b) a b| ≤
      L * (b - a) ^ ((n + 1 : ℕ) + θ) / (n + 1).factorial := by
  obtain ⟨y, hy, he⟩ := taylor_remainder_eq_derivative_difference hab hf
  have hba : 0 < b - a := sub_pos.mpr hab
  have hya : 0 ≤ y - a := sub_nonneg.mpr hy.1.le
  have hp : |y - a| ^ θ ≤ (b - a) ^ θ := by
    rw [abs_of_nonneg hya]
    exact Real.rpow_le_rpow hya (by linarith [hy.2]) hθ
  have hm := (hholder y ⟨hy.1.le, hy.2.le⟩).trans
    (mul_le_mul_of_nonneg_left hp hL)
  rw [he, abs_div, abs_mul, abs_of_nonneg (pow_nonneg hba.le _), Nat.abs_cast]
  calc
    _ ≤ (L * (b - a) ^ θ) * (b - a) ^ (n + 1) / (n + 1).factorial :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hm (pow_nonneg hba.le _)) (Nat.cast_nonneg _)
    _ = _ := by
      rw [Real.rpow_add hba, Real.rpow_natCast]
      ring

theorem holder_taylor_remainder_zero {f : ℝ → ℝ} {a b L θ : ℝ}
    (hab : a ≤ b) (hholder : |f b - f a| ≤ L * |b - a| ^ θ) :
    |f b - taylorWithinEval f 0 (Icc a b) a b| ≤ L * (b - a) ^ θ := by
  simpa only [taylor_within_zero_eval, abs_of_nonneg (sub_nonneg.mpr hab)] using hholder

end CausalLowerbound.UpperBound

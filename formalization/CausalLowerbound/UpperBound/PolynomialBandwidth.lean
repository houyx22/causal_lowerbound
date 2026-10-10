import CausalLowerbound.UpperBound.Rates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Positive polynomial bandwidths, including n = 0.  Using n + 1 only
changes fixed constants and avoids exceptional definitions at zero. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace CausalLowerbound.UpperBound

def polynomialBandwidth (a : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-a)

theorem polynomialBandwidth_pos (a : ℝ) (n : ℕ) : 0 < polynomialBandwidth a n :=
  Real.rpow_pos_of_pos (by positivity) _

theorem polynomialBandwidth_rpow (a b : ℝ) (n : ℕ) :
    polynomialBandwidth a n ^ b = polynomialBandwidth (a * b) n := by
  unfold polynomialBandwidth
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem polynomialBandwidth_pow (a : ℝ) (k n : ℕ) :
    polynomialBandwidth a n ^ k = polynomialBandwidth (a * k) n := by
  rw [← Real.rpow_natCast, polynomialBandwidth_rpow]

theorem polynomialBandwidth_mul (a b : ℝ) (n : ℕ) :
    polynomialBandwidth a n * polynomialBandwidth b n = polynomialBandwidth (a + b) n := by
  unfold polynomialBandwidth
  rw [← Real.rpow_add (by positivity)]
  congr 1
  ring

theorem polynomialBandwidth_div (a b : ℝ) (n : ℕ) :
    polynomialBandwidth a n / polynomialBandwidth b n = polynomialBandwidth (a - b) n := by
  unfold polynomialBandwidth
  rw [← Real.rpow_sub (by positivity)]
  congr 1
  ring

@[simp] theorem polynomialBandwidth_zero (n : ℕ) : polynomialBandwidth 0 n = 1 := by
  simp [polynomialBandwidth]

@[simp] theorem polynomialBandwidth_one (n : ℕ) : polynomialBandwidth 1 n = 1 / ((n : ℝ) + 1) := by
  simp [polynomialBandwidth, Real.rpow_neg_one, one_div]

theorem polynomialBandwidth_antitone {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    polynomialBandwidth b n ≤ polynomialBandwidth a n :=
  Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_left (Nat.cast_nonneg n)) (neg_le_neg hab)

theorem polynomialBandwidth_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (polynomialBandwidth a) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_neg_atTop ha).comp hn

theorem polynomialBandwidth_div_tendsto {a b : ℝ} (hab : b < a) :
    Tendsto (fun n => polynomialBandwidth a n / polynomialBandwidth b n) atTop (𝓝 0) := by
  simp_rw [polynomialBandwidth_div]
  exact polynomialBandwidth_tendsto (sub_pos.mpr hab)

theorem twoScaleModulus_polynomial (α b c : ℝ) (n : ℕ) :
    twoScaleModulus α (polynomialBandwidth b n) (polynomialBandwidth c n) =
      polynomialBandwidth (b * min α 1 + c * max (α - 1) 0) n := by
  unfold twoScaleModulus
  rw [polynomialBandwidth_rpow, polynomialBandwidth_rpow, polynomialBandwidth_mul]

theorem twoScaleModulus_polynomial_tendsto {α b c : ℝ} (hα : 0 < α) (hb : 0 < b) (hc : 0 ≤ c) :
    Tendsto (fun n => twoScaleModulus α (polynomialBandwidth b n) (polynomialBandwidth c n))
      atTop (𝓝 0) := by
  simp_rw [twoScaleModulus_polynomial]
  apply polynomialBandwidth_tendsto
  exact add_pos_of_pos_of_nonneg (mul_pos hb (lt_min hα zero_lt_one))
    (mul_nonneg hc (le_max_right _ _))

theorem reciprocal_sampleSize_le_bandwidth {n : ℕ} (hn : 1 ≤ n) :
    1 / (n : ℝ) ≤ 2 * polynomialBandwidth 1 n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  rw [polynomialBandwidth_one, mul_one_div]
  apply (div_le_div_iff₀ hp (by positivity)).mpr
  nlinarith

end CausalLowerbound.UpperBound

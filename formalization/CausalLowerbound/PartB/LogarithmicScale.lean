import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! The concrete polynomial amplitude and logarithmic taper scale. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology BigOperators

namespace CausalLowerbound.PartB

def logScale (x : ℝ) : ℝ := 1 + Real.log x
def polynomialAmplitude (a x : ℝ) : ℝ := x ^ (-a)
def logarithmicThreshold (a B x : ℝ) : ℝ := polynomialAmplitude a x * logScale x ^ B

theorem logScale_one_le {x : ℝ} (hx : 1 ≤ x) : 1 ≤ logScale x := by
  have := Real.log_nonneg hx
  dsimp [logScale]
  linarith

theorem logScale_pos {x : ℝ} (hx : 1 ≤ x) : 0 < logScale x :=
  lt_of_lt_of_le zero_lt_one (logScale_one_le hx)

theorem polynomialAmplitude_pos (a : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < polynomialAmplitude a x := Real.rpow_pos_of_pos hx _

theorem logarithmicThreshold_pos (a B : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    0 < logarithmicThreshold a B x :=
  mul_pos (polynomialAmplitude_pos a (lt_of_lt_of_le zero_lt_one hx))
    (Real.rpow_pos_of_pos (logScale_pos hx) _)

theorem amplitude_threshold_ratio (a B : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    polynomialAmplitude a x / logarithmicThreshold a B x = logScale x ^ (-B) := by
  rw [logarithmicThreshold, div_mul_cancel_left₀
    (polynomialAmplitude_pos a (lt_of_lt_of_le zero_lt_one hx)).ne',
    Real.rpow_neg (logScale_pos hx).le]

theorem logScale_tendsto : Tendsto logScale atTop atTop :=
  tendsto_atTop_mono (fun x => by dsimp [logScale]; linarith) Real.tendsto_log_atTop

theorem logarithmicThreshold_tendsto (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B) :
    Tendsto (logarithmicThreshold a B) atTop (𝓝 0) := by
  have hr := (isLittleO_log_rpow_rpow_atTop B ha).tendsto_div_nhds_zero
  have hb : Tendsto (fun x : ℝ => (2 : ℝ) ^ B * (Real.log x ^ B / x ^ a)) atTop (𝓝 0) := by
    simpa using hr.const_mul ((2 : ℝ) ^ B)
  apply squeeze_zero' _ _ hb
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact (logarithmicThreshold_pos a B hx).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hl
    have hp : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hc : logScale x ≤ 2 * Real.log x := by dsimp [logScale]; linarith
    have he := Real.rpow_le_rpow (logScale_pos hx).le hc hB
    rw [Real.mul_rpow (by norm_num) (by linarith)] at he
    have hm := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Real.rpow_pos_of_pos hp a).le)
    simpa only [logarithmicThreshold, polynomialAmplitude, Real.rpow_neg hp.le,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hm

theorem threshold_log_bound (a B : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B)
    {x : ℝ} (hx : 1 ≤ x) :
    1 + Real.log (1 / logarithmicThreshold a B x) ≤ (1 + a) * logScale x := by
  have hp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hΛ := logScale_pos hx
  have hlogΛ : 0 ≤ Real.log (logScale x) := Real.log_nonneg (logScale_one_le hx)
  have hAmp := polynomialAmplitude_pos a hp
  rw [one_div, Real.log_inv, logarithmicThreshold,
    Real.log_mul hAmp.ne' (Real.rpow_pos_of_pos hΛ B).ne',
    polynomialAmplitude, Real.log_rpow hp, Real.log_rpow hΛ]
  dsimp [logScale] at hlogΛ ⊢
  nlinarith [mul_nonneg hB hlogΛ]

theorem power_sum_from_two (D : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (∑ j ∈ Finset.Icc 2 D, r ^ j) ≤ (D + 1 : ℝ) * r ^ 2 := by
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 2 D, r ^ 2 := Finset.sum_le_sum (fun j hj =>
      pow_le_pow_of_le_one hr hr1 (Finset.mem_Icc.mp hj).1)
    _ = ((Finset.Icc 2 D).card : ℝ) * r ^ 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
      exact_mod_cast (show (Finset.Icc 2 D).card ≤ D + 1 by rw [Nat.card_Icc]; omega)) (sq_nonneg r)

theorem logarithmic_majorant_bound (E D : ℕ) (a B : ℝ) (ha : 0 ≤ a) (hB : 0 ≤ B)
    {x : ℝ} (hx : 1 ≤ x) (ht : logarithmicThreshold a B x ≤ 1) :
    (1 + Real.log (1 / logarithmicThreshold a B x)) ^ E *
        (∑ j ∈ Finset.Icc 2 D, (polynomialAmplitude a x / logarithmicThreshold a B x) ^ j) ≤
      ((1 + a) ^ E * (D + 1)) * logScale x ^ ((E : ℝ) - 2 * B) := by
  have htpos := logarithmicThreshold_pos a B hx
  have hn : 0 ≤ 1 + Real.log (1 / logarithmicThreshold a B x) := by
    have := Real.log_nonneg ((le_div_iff₀ htpos).mpr (by simpa using ht))
    linarith
  have hpow := pow_le_pow_left₀ hn (threshold_log_bound a B ha hB hx) E
  rw [amplitude_threshold_ratio a B hx]
  have hr : 0 ≤ logScale x ^ (-B) := (Real.rpow_pos_of_pos (logScale_pos hx) _).le
  have hr1 : logScale x ^ (-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (logScale_one_le hx) (neg_nonpos.mpr hB)
  have hs := power_sum_from_two D hr hr1
  have hm := mul_le_mul hpow hs
    (Finset.sum_nonneg (fun j _ => pow_nonneg hr j))
    (pow_nonneg (mul_nonneg (by linarith) (logScale_pos hx).le) E)
  apply hm.trans_eq
  have he : logScale x ^ E * (logScale x ^ (-B)) ^ 2 =
      logScale x ^ ((E : ℝ) - 2 * B) := by
    rw [← Real.rpow_natCast _ E, ← Real.rpow_mul_natCast (logScale_pos hx).le,
      ← Real.rpow_add (logScale_pos hx)]
    congr 1
    push_cast
    ring
  calc
    _ = ((1 + a) ^ E * (D + 1)) * (logScale x ^ E * (logScale x ^ (-B)) ^ 2) := by
      rw [mul_pow]; ring
    _ = _ := by rw [he]

theorem logarithmic_majorant_tendsto (E : ℕ) (B : ℝ) (hB : (E : ℝ) < 2 * B) :
    Tendsto (fun x => logScale x ^ ((E : ℝ) - 2 * B)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hB)).comp logScale_tendsto
  simpa only [neg_sub] using h

end CausalLowerbound.PartB

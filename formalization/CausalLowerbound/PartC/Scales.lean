import CausalLowerbound.PartC.ScaleBudget

/-! Physical scales and amplitudes for the mixed case. A common positive
amplitude constant is enough for both nuisances, and gives the pointwise
inequality `shift ≤ rough` throughout the scale range. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace CausalLowerbound.PartC

def signalScale (A d γ s ε : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (-(rateExponent A d γ s + ε))
def coarseScale (A d γ s ε : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (-((rateExponent A d γ s + ε) / γ))
def carrierScale (A d ε : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-carrierExponent A d ε)
def jitterScale (A d γ s ε : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (-jitterExponent A d γ s ε)
def roughAmplitude (c u r t : ℝ) : ℝ := c * (t * r) ^ u
def shiftAmplitude (c v r t : ℝ) : ℝ := c * r ^ v * t

theorem polynomial_scales_balanced (A γ s z ξ x : ℝ) (hx : 1 ≤ x)
    (hγ : 0 < γ) (hs : 0 < s) (hz : 0 ≤ z) (hξ : z / γ ≤ ξ)
    (hp : 0 ≤ (z - ξ * A) / (2 * s)) :
    let r := x ^ (-ξ)
    let h := x ^ (-(z / γ))
    let t := x ^ (-((z - ξ * A) / (2 * s)))
    0 < r ∧ r ≤ h ∧ h ≤ 1 ∧ 0 < t ∧ t ≤ 1 ∧ h ^ γ = r ^ A * t ^ (2 * s) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  dsimp
  refine ⟨Real.rpow_pos_of_pos hx0 _, Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hξ),
    Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr (div_nonneg hz hγ.le)),
    Real.rpow_pos_of_pos hx0 _, Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr hp), ?_⟩
  simp only [← Real.rpow_mul hx0.le]
  rw [← Real.rpow_add hx0]
  congr 1
  field_simp <;> ring

theorem scales_balanced (A d γ s ε : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hs : 0 < s) (hreg : A * (2 + d / γ) < d) (hε : 0 < ε)
    (hεsmall : ε < γ / d - rateExponent A d γ s) (n : ℕ) :
    0 < carrierScale A d ε n ∧ carrierScale A d ε n ≤ coarseScale A d γ s ε n ∧
      coarseScale A d γ s ε n ≤ 1 ∧ 0 < jitterScale A d γ s ε n ∧
      jitterScale A d γ s ε n ≤ 1 ∧
      coarseScale A d γ s ε n ^ γ = carrierScale A d ε n ^ A * jitterScale A d γ s ε n ^ (2 * s) := by
  have ho := concrete_scale_exponents A d γ s ε hA hd hγ hs hreg hε hεsmall
  exact polynomial_scales_balanced A γ s (rateExponent A d γ s + ε) (carrierExponent A d ε)
    ((n : ℝ) + 1) (le_add_of_nonneg_left (Nat.cast_nonneg n)) hγ hs ho.1.le ho.2.1.le ho.2.2.le

theorem coarseScale_power (A d γ s ε : ℝ) (hγ : γ ≠ 0) (n : ℕ) :
    coarseScale A d γ s ε n ^ γ = signalScale A d γ s ε n := by
  unfold coarseScale signalScale
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  congr 1
  field_simp

theorem mixed_amplitudes_balance (c u v r t δ : ℝ) (hr : 0 < r) (ht : 0 < t)
    (hbalance : r ^ (u + v) * t ^ (u + 1) = δ) :
    roughAmplitude c u r t * shiftAmplitude c v r t = c ^ 2 * δ := by
  calc
    _ = c ^ 2 * (r ^ u * r ^ v) * (t ^ u * t ^ (1 : ℝ)) := by
      unfold roughAmplitude shiftAmplitude
      rw [Real.mul_rpow ht.le hr.le, Real.rpow_one]
      ring
    _ = c ^ 2 * (r ^ (u + v) * t ^ (u + 1)) := by
      rw [← Real.rpow_add hr, ← Real.rpow_add ht]
      ring
    _ = _ := by rw [hbalance]

theorem shiftAmplitude_le_roughAmplitude (c u v r t : ℝ) (hc : 0 ≤ c)
    (hr : 0 < r) (hr1 : r ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hu : u ≤ 1) (huv : u ≤ v) : shiftAmplitude c v r t ≤ roughAmplitude c u r t := by
  have hrv : r ^ v ≤ r ^ u := Real.rpow_le_rpow_of_exponent_ge hr hr1 huv
  have htt : t ≤ t ^ u := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1 hu
  unfold shiftAmplitude roughAmplitude
  rw [Real.mul_rpow ht.le hr.le]
  have hh := mul_le_mul hrv htt ht.le (Real.rpow_nonneg hr.le u)
  convert mul_le_mul_of_nonneg_left hh hc using 1 <;> ring

theorem shiftAmplitude_square_le_product (c u v r t : ℝ) (hc : 0 ≤ c)
    (hr : 0 < r) (hr1 : r ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hu : u ≤ 1) (huv : u ≤ v) :
    shiftAmplitude c v r t ^ 2 ≤ roughAmplitude c u r t * shiftAmplitude c v r t := by
  have hn : 0 ≤ shiftAmplitude c v r t := by unfold shiftAmplitude; positivity
  simpa only [pow_two] using mul_le_mul_of_nonneg_right
    (shiftAmplitude_le_roughAmplitude c u v r t hc hr hr1 ht ht1 hu huv) hn

theorem carrierScale_tendsto (A d ε : ℝ) (hA : 0 < A) (hd : 0 < d) (hε : 0 ≤ ε) :
    Tendsto (carrierScale A d ε) atTop (𝓝 0) := by
  have hξ : 0 < carrierExponent A d ε := by
    unfold carrierExponent PartB.carrierExponent
    exact add_pos_of_pos_of_nonneg (one_div_pos.mpr hd) (div_nonneg hε (by positivity))
  simpa only [carrierScale, Real.rpow_zero, mul_one, Nat.cast_add, Nat.cast_one] using
    PartB.polynomial_log_tendsto (carrierExponent A d ε) 0 hξ

theorem jitterScale_tendsto (A d γ s ε : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hs : 0 < s) (hreg : A * (2 + d / γ) < d) (hε : 0 < ε)
    (hεsmall : ε < γ / d - rateExponent A d γ s) :
    Tendsto (jitterScale A d γ s ε) atTop (𝓝 0) := by
  have hp := (concrete_scale_exponents A d γ s ε hA hd hγ hs hreg hε hεsmall).2.2
  simpa only [jitterScale, Real.rpow_zero, mul_one, Nat.cast_add, Nat.cast_one] using
    PartB.polynomial_log_tendsto (jitterExponent A d γ s ε) 0 hp

theorem taperThreshold_bounds (t θ : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    0 < t ^ (1 - θ) ∧ t ≤ t ^ (1 - θ) ∧ t ^ (1 - θ) ≤ 1 := by
  refine ⟨Real.rpow_pos_of_pos ht _, ?_, Real.rpow_le_one ht.le ht1 (by linarith)⟩
  simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_ge ht ht1 (show 1 - θ ≤ 1 by linarith)

end CausalLowerbound.PartC

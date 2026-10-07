import CausalLowerbound.PartC.RateLedgers

/-! A simultaneous budget for subcritical volume estimates and small power
losses in the assignment multiplier. This changes the taper threshold to
`t^(1-θ)`. No sharp logarithmic bad-volume or multiplier bound is needed
provided the concrete analytic estimates meet the interfaces below. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace CausalLowerbound.PartC

structure PowerBudget (d p margin : ℝ) where
  volumeExponent : ℝ
  taperGap : ℝ
  multiplierLoss : ℝ
  volume_pos : 0 < volumeExponent
  volume_lt : volumeExponent < d
  gap_pos : 0 < taperGap
  gap_lt_one : taperGap < 1
  multiplier_pos : 0 < multiplierLoss
  multiplier_small : d * multiplierLoss < taperGap / 2
  volume_small : p * (d - volumeExponent * (1 - taperGap)) < margin / 2

theorem nonempty_powerBudget (d p margin : ℝ) (hd : 0 < d) (hp : 0 < p)
    (hm : 0 < margin) : Nonempty (PowerBudget d p margin) := by
  obtain ⟨a, ha, hsmall⟩ := exists_between (lt_min hd (div_pos hm (by positivity : 0 < 4 * p)))
  have had : a < d := hsmall.trans_le (min_le_left _ _)
  have hap : p * a < margin / 4 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 4 * p)).mp
      (hsmall.trans_le (min_le_right _ _))
    nlinarith
  have hgap : 0 < a / d := div_pos ha hd
  have hmult : d * ((a / d) / (4 * d)) = (a / d) / 4 := by field_simp; ring
  have hloss : d - (d - a) * (1 - a / d) = 2 * a - a ^ 2 / d := by
    field_simp
    ring
  refine ⟨⟨d - a, a / d, (a / d) / (4 * d), by linarith, by linarith,
    hgap, (div_lt_one hd).mpr had, by positivity, ?_, ?_⟩⟩
  · rw [hmult]
    linarith
  · rw [hloss]
    nlinarith [mul_nonneg hp.le (div_nonneg (sq_nonneg a) hd.le)]

namespace PowerBudget
variable {d p margin : ℝ} (b : PowerBudget d p margin)

theorem carrier_exponent_pos (hp : 0 < p) : 0 < p * (b.taperGap - d * b.multiplierLoss) :=
  mul_pos hp (by linarith [b.multiplier_small, b.gap_pos])

theorem ghost_exponent_neg (hm : 0 < margin) :
    -margin + p * (d - b.volumeExponent * (1 - b.taperGap)) < 0 := by
  linarith [b.volume_small]

theorem carrier_tendsto (hp : 0 < p) (B : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-(p * (b.taperGap - d * b.multiplierLoss))) *
      PartB.logScale (n + 1) ^ B) atTop (𝓝 0) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    PartB.polynomial_log_tendsto _ B (b.carrier_exponent_pos hp)

theorem ghost_tendsto (hm : 0 < margin) (B : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^
      (-margin + p * (d - b.volumeExponent * (1 - b.taperGap))) *
      PartB.logScale (n + 1) ^ B) atTop (𝓝 0) := by
  simpa only [neg_neg, Nat.cast_add, Nat.cast_one] using
    PartB.polynomial_log_tendsto _ B (neg_pos.mpr (b.ghost_exponent_neg hm))

end PowerBudget

def relaxedGhostMass (A d γ s ε v θ x : ℝ) : ℝ :=
  x * (x ^ (-((rateExponent A d γ s + ε) / γ))) ^ d *
    ((x ^ (-jitterExponent A d γ s ε)) ^ (1 - θ)) ^ v *
      (x ^ (-(rateExponent A d γ s + ε))) ^ (2 : ℕ)

theorem relaxedGhostMass_eq (A d γ s ε v θ x : ℝ) (hx : 0 < x)
    (hA : A ≠ 0) (hd : d ≠ 0) (hγ : γ ≠ 0) (hs : s ≠ 0)
    (hD : rateDenominator d γ s ≠ 0) :
    relaxedGhostMass A d γ s ε v θ x =
      x ^ (-rateMargin d γ s ε + jitterExponent A d γ s ε * (d - v * (1 - θ))) := by
  unfold relaxedGhostMass
  rw [← Real.rpow_natCast (n := 2)]
  simp only [← Real.rpow_mul hx.le]
  calc
    _ = x ^ (1 - (rateExponent A d γ s + ε) * d / γ -
        jitterExponent A d γ s ε * (1 - θ) * v - 2 * (rateExponent A d γ s + ε)) := by
      conv_lhs => arg 1; arg 1; arg 1; rw [← Real.rpow_one x]
      rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 1
      push_cast
      ring
    _ = _ := by
      congr 1
      linear_combination (rate_exponent_ledgers A d γ s ε hA hd hγ hs hD).1

theorem carrierRatio_eq (p d θ η x : ℝ) (hx : 0 < x) :
    (x ^ (-p) / (x ^ (-p)) ^ (1 - θ)) * ((x ^ (-p)) ^ d) ^ (-η) =
      x ^ (-(p * (θ - d * η))) := by
  simp only [← Real.rpow_mul hx.le]
  rw [← Real.rpow_sub hx, ← Real.rpow_add hx]
  congr 1
  ring

theorem exists_relaxed_rate_control (A d γ s ε : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hs : 0 < s) (hreg : A * (2 + d / γ) < d) (hε : 0 < ε)
    (hεsmall : ε < γ / d - rateExponent A d γ s) :
    ∃ b : PowerBudget d (jitterExponent A d γ s ε) (rateMargin d γ s ε), ∀ B : ℝ,
      Tendsto (fun n : ℕ => relaxedGhostMass A d γ s ε b.volumeExponent b.taperGap (n + 1) *
        PartB.logScale (n + 1) ^ B) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ =>
        (((n : ℝ) + 1) ^ (-jitterExponent A d γ s ε) /
          (((n : ℝ) + 1) ^ (-jitterExponent A d γ s ε)) ^ (1 - b.taperGap)) *
        (((((n : ℝ) + 1) ^ (-jitterExponent A d γ s ε)) ^ d) ^ (-b.multiplierLoss)) *
        PartB.logScale (n + 1) ^ B) atTop (𝓝 0) := by
  have hp := (concrete_scale_exponents A d γ s ε hA hd hγ hs hreg hε hεsmall).2.2
  have hm := rateMargin_pos d γ s ε hd hγ hs hε
  obtain ⟨b⟩ := nonempty_powerBudget d (jitterExponent A d γ s ε) (rateMargin d γ s ε) hd hp hm
  refine ⟨b, fun B => ⟨?_, ?_⟩⟩
  · apply (b.ghost_tendsto hm B).congr'
    filter_upwards [] with n
    rw [relaxedGhostMass_eq A d γ s ε _ _ _ (by positivity) hA.ne' hd.ne' hγ.ne' hs.ne'
      (rateDenominator_pos d γ s hd hγ hs).ne']
  · apply (b.carrier_tendsto hp B).congr'
    filter_upwards [] with n
    rw [carrierRatio_eq _ _ _ _ _ (by positivity)]

end CausalLowerbound.PartC

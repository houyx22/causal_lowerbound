import CausalLowerbound.PartB.RateLedgers

/-! The epsilon margin absorbs the arbitrarily small power loss in the
concrete bad-volume estimate. Both actual error monomials still vanish. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace CausalLowerbound.PartB

theorem jitter_power_loss (x p d s : ℝ) (hx : 0 < x) :
    (x ^ (-p)) ^ s = (x ^ (-p)) ^ d * x ^ ((d - s) * p) := by
  rw [← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
  congr 1
  ring

theorem exists_subcritical_rate_control (A d γ ε : ℝ)
    (hA : 0 < A) (hd : 0 < d) (hγ : 0 < γ) (hreg : A * (2 + d / γ) < d)
    (hε : 0 < ε) (hεsmall : ε < γ / d - rateExponent A d γ) :
    ∃ s : ℝ, 0 < s ∧ s < d ∧ ∀ B : ℝ,
      Tendsto (fun n : ℕ => singletonMass A d γ ε (n + 1) *
        ((n : ℝ) + 1) ^ ((d - s) * jitterExponent A d γ ε) * logScale (n + 1) ^ B)
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => collisionMass A d γ ε (n + 1) *
        ((n : ℝ) + 1) ^ ((d - s) * jitterExponent A d γ ε) * logScale (n + 1) ^ B)
        atTop (𝓝 0) := by
  have hp := (concrete_scale_exponents A d γ ε hA hd hγ hreg hε hεsmall).2.2
  have hneg := (rate_ledger_exponents_negative A d γ ε hA hd hγ hε).1
  let κ := ε * (rateDenominator d γ - d / 2) / 2
  have hκ : 0 < κ := by dsimp [κ]; linarith
  obtain ⟨η, hη, hηsmall⟩ := exists_between (lt_min hd (div_pos hκ hp))
  have hηd : η < d := hηsmall.trans_le (min_le_left _ _)
  have hηκ : η * jitterExponent A d γ ε < κ :=
    (lt_div_iff₀ hp).mp (hηsmall.trans_le (min_le_right _ _))
  refine ⟨d - η, by linarith, by linarith, ?_⟩
  intro B
  have hD := (rateDenominator_pos d γ hd hγ).ne'
  have h₁ : -ε * (rateDenominator d γ - d / 2) / 2 +
      (d - (d - η)) * jitterExponent A d γ ε < 0 := by
    dsimp [κ] at hηκ
    linarith
  have h₂ : -ε * (rateDenominator d γ - d / 2) / 2 - d * ε / (2 * A) +
      (d - (d - η)) * jitterExponent A d γ ε < 0 := by
    linarith [div_pos (mul_pos hd hε) (mul_pos two_pos hA)]
  have ht (e : ℝ) (he : e < 0) :
      Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ e * logScale (n + 1) ^ B) atTop (𝓝 0) := by
    simpa only [neg_neg, Nat.cast_add, Nat.cast_one] using polynomial_log_tendsto (-e) B (neg_pos.mpr he)
  constructor
  · apply (ht _ h₁).congr'
    filter_upwards [] with n
    rw [singletonMass_eq A d γ ε _ (by positivity) hA.ne' hd.ne' hγ.ne' hD,
      ← Real.rpow_add (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  · apply (ht _ h₂).congr'
    filter_upwards [] with n
    rw [collisionMass_eq A d γ ε _ (by positivity) hA.ne' hd.ne' hγ.ne' hD,
      ← Real.rpow_add (by positivity : (0 : ℝ) < (n : ℝ) + 1)]

end CausalLowerbound.PartB

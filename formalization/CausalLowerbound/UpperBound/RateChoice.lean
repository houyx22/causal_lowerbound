import CausalLowerbound.UpperBound.Rates

/-! The low- and high-smoothness choices discharge every numerical exponent
condition used by the uniform estimator theorem, including the threshold. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.UpperBound

def upperRateExponent (α β D γ : ℝ) : ℝ :=
  if (α + β) / 2 < smoothnessThreshold D γ then
    rateExponent ((α + β) / 2) ((min α 1 + min β 1) / 2) D γ
  else γ / (2 * γ + D)

theorem upperRateExponent_of_low {α β D γ : ℝ}
    (hlow : (α + β) / 2 < smoothnessThreshold D γ) :
    upperRateExponent α β D γ =
      rateExponent ((α + β) / 2) ((min α 1 + min β 1) / 2) D γ := if_pos hlow

theorem upperRateExponent_of_high {α β D γ : ℝ}
    (hhigh : smoothnessThreshold D γ ≤ (α + β) / 2) :
    upperRateExponent α β D γ = γ / (2 * γ + D) := if_neg (not_lt.mpr hhigh)

theorem upperRateExponent_low_large_nuisance {α β D γ : ℝ}
    (hα : 1 ≤ α) (hβ : 1 ≤ β) (hlow : (α + β) / 2 < smoothnessThreshold D γ) :
    upperRateExponent α β D γ = (α + β + 2) / (D + 4 + 2 * D / γ) := by
  rw [upperRateExponent_of_low hlow, min_eq_right hα, min_eq_right hβ]
  norm_num [rateExponent, rateDenominator]
  congr 1
  ring

theorem upperRateExponent_pos {α β D γ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hD : 0 < D) (hγ : 0 < γ) : 0 < upperRateExponent α β D γ := by
  unfold upperRateExponent
  split_ifs
  · exact rateExponent_pos (by positivity)
      (div_pos (add_pos (lt_min hα zero_lt_one) (lt_min hβ zero_lt_one)) (by norm_num)) hD hγ
  · exact div_pos hγ (by positivity)

theorem exists_upper_bandwidth_exponents {α β D γ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hD : 0 < D) (hγ : 0 < γ) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 / D ∧ 1 / D ≤ b ∧
      upperRateExponent α β D γ ≤ a * γ ∧
      upperRateExponent α β D γ ≤ b * (min α 1 + min β 1) +
        (1 / D) * (α + β - (min α 1 + min β 1)) ∧
      2 * upperRateExponent α β D γ ≤ 1 - a * D ∧
      2 * upperRateExponent α β D γ ≤ 2 - (a + b) * D := by
  let s := (α + β) / 2
  let t := (min α 1 + min β 1) / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have ht : 0 < t := div_pos (add_pos (lt_min hα zero_lt_one) (lt_min hβ zero_lt_one)) (by norm_num)
  by_cases hlow : s < smoothnessThreshold D γ
  · have he : upperRateExponent α β D γ = rateExponent s t D γ := if_pos hlow
    rw [he]
    let ρ := rateExponent s t D γ
    let b := fineExponent s t D γ
    have hρ : 0 < ρ := rateExponent_pos hs ht hD hγ
    have hscale := low_scale_ordering hs ht hD hγ hlow
    have hbalance := rate_balances (s := s) ht hD hγ
    have hordinary := ordinary_fluctuation_faster hs ht hD hγ hlow
    refine ⟨ρ / γ, b, div_pos hρ hγ, hscale.2, hscale.1.le, ?_, ?_, ?_, ?_⟩
    · exact le_of_eq (div_mul_cancel₀ ρ hγ.ne').symm
    · have hnum : b * (min α 1 + min β 1) + (1 / D) * (α + β - (min α 1 + min β 1)) =
          2 * t * b + 2 * (s - t) / D := by dsimp [s, t]; ring
      rw [hnum]
      exact hbalance.1.symm.le
    · change ρ < (1 - ρ * D / γ) / 2 at hordinary
      have hnum : ρ / γ * D = ρ * D / γ := by ring
      rw [hnum]
      linarith
    · have hb : 1 - (ρ * D / γ + b * D) / 2 = ρ := hbalance.2
      have hnum : (ρ / γ + b) * D = ρ * D / γ + b * D := by ring
      rw [hnum]
      linarith
  · have hhigh : smoothnessThreshold D γ ≤ s := le_of_not_gt hlow
    have he : upperRateExponent α β D γ = γ / (2 * γ + D) := if_neg hlow
    rw [he]
    have hden : 0 < 2 * γ + D := by positivity
    refine ⟨1 / (2 * γ + D), 1 / D, one_div_pos.mpr hden, ?_, le_rfl, ?_, ?_, ?_, ?_⟩
    · apply (div_lt_div_iff₀ hden hD).mpr
      nlinarith
    · apply le_of_eq
      ring
    · have hbound := high_regime_bias_ordering hD hγ hhigh
      have hnum : (1 / D) * (min α 1 + min β 1) +
          (1 / D) * (α + β - (min α 1 + min β 1)) = 2 * s / D := by dsimp [s]; ring
      rw [hnum]
      exact hbound
    · apply le_of_eq
      field_simp
    · apply le_of_eq
      field_simp <;> ring

end CausalLowerbound.UpperBound

import CausalLowerbound.UpperBound.TwoScaleContrast
import CausalLowerbound.PartB.RateRegime

/-! The upper-bound exponent and its scale balances for arbitrary positive
smoothness.  In the high-smoothness nuisance case the exponent agrees exactly
with the existing Part B definition. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.UpperBound

def rateDenominator (t d γ : ℝ) : ℝ := d + 4 * t + 2 * d * t / γ

def rateExponent (s t d γ : ℝ) : ℝ := 2 * (s + t) / rateDenominator t d γ

def fineExponent (s t d γ : ℝ) : ℝ :=
  (rateExponent s t d γ - 2 * (s - t) / d) / (2 * t)

def smoothnessThreshold (d γ : ℝ) : ℝ := d * γ / (2 * (2 * γ + d))

theorem rateDenominator_pos {t d γ : ℝ} (ht : 0 < t) (hd : 0 < d) (hγ : 0 < γ) :
    0 < rateDenominator t d γ := by unfold rateDenominator; positivity

theorem rateExponent_pos {s t d γ : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hd : 0 < d) (hγ : 0 < γ) :
    0 < rateExponent s t d γ :=
  div_pos (by positivity) (rateDenominator_pos ht hd hγ)

theorem low_regime_inequality {s d γ : ℝ} (hd : 0 < d) (hγ : 0 < γ)
    (hlow : s < smoothnessThreshold d γ) : 2 * s * (2 + d / γ) < d := by
  have hh := (lt_div_iff₀ (show 0 < 2 * (2 * γ + d) by positivity)).mp hlow
  apply (mul_lt_mul_right hγ).mp
  calc
    2 * s * (2 + d / γ) * γ = 2 * s * (2 * γ + d) := by field_simp
    _ < d * γ := by nlinarith [hh]

theorem low_rate_ordering {s t d γ : ℝ}
    (_hs : 0 < s) (ht : 0 < t) (hd : 0 < d) (hγ : 0 < γ)
    (hlow : s < smoothnessThreshold d γ) :
    2 * s / d < rateExponent s t d γ ∧
      rateExponent s t d γ < γ / (2 * γ + d) := by
  have hD := rateDenominator_pos ht hd hγ
  have hreg := low_regime_inequality hd hγ hlow
  have hreg' := (lt_div_iff₀ (show 0 < 2 * (2 * γ + d) by positivity)).mp hlow
  constructor
  · apply (div_lt_div_iff₀ hd hD).mpr
    have hh := mul_lt_mul_of_pos_left hreg (show 0 < 2 * t by positivity)
    dsimp [rateDenominator]
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith [hh]
  · apply (div_lt_div_iff₀ hD (show 0 < 2 * γ + d by positivity)).mpr
    have he : γ * rateDenominator t d γ = γ * d + 4 * γ * t + 2 * d * t := by
      unfold rateDenominator
      field_simp
      ring
    rw [he]
    nlinarith [hreg']

theorem low_scale_ordering {s t d γ : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hd : 0 < d) (hγ : 0 < γ)
    (hlow : s < smoothnessThreshold d γ) :
    1 / d < fineExponent s t d γ ∧ rateExponent s t d γ / γ < 1 / d := by
  obtain ⟨hrlo, hrhi⟩ := low_rate_ordering hs ht hd hγ hlow
  constructor
  · apply (lt_div_iff₀ (show 0 < 2 * t by positivity)).mpr
    have he : (1 / d) * (2 * t) + 2 * (s - t) / d = 2 * s / d := by ring
    linarith
  · apply (div_lt_div_iff₀ hγ hd).mpr
    have hcmp : γ / (2 * γ + d) < γ / d := by
      apply (div_lt_div_iff₀ (by positivity) hd).mpr
      nlinarith [sq_pos_of_pos hγ]
    have hh := (lt_div_iff₀ hd).mp (hrhi.trans hcmp)
    simpa using hh

/-- Both nuisance bias and the pair-overlap fluctuation have exponent ρ. -/
theorem rate_balances {s t d γ : ℝ} (ht : 0 < t) (hd : 0 < d) (hγ : 0 < γ) :
    2 * t * fineExponent s t d γ + 2 * (s - t) / d = rateExponent s t d γ ∧
      1 - (rateExponent s t d γ * d / γ + fineExponent s t d γ * d) / 2 =
        rateExponent s t d γ := by
  have hD : rateDenominator t d γ ≠ 0 := ne_of_gt (rateDenominator_pos ht hd hγ)
  have ht' : t ≠ 0 := ne_of_gt ht
  have hd' : d ≠ 0 := ne_of_gt hd
  have hγ' : γ ≠ 0 := ne_of_gt hγ
  constructor
  · unfold fineExponent
    field_simp
    ring
  · have hr : rateExponent s t d γ * rateDenominator t d γ = 2 * (s + t) :=
      div_mul_cancel₀ _ hD
    unfold rateDenominator at hr
    unfold fineExponent
    field_simp at hr ⊢
    nlinarith [hr]

theorem ordinary_fluctuation_faster {s t d γ : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hd : 0 < d) (hγ : 0 < γ)
    (hlow : s < smoothnessThreshold d γ) :
    rateExponent s t d γ < (1 - rateExponent s t d γ * d / γ) / 2 := by
  have hh := (lt_div_iff₀ (show 0 < 2 * γ + d by positivity)).mp
    (low_rate_ordering hs ht hd hγ hlow).2
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply (mul_lt_mul_right hγ).mp
  have he : (1 - rateExponent s t d γ * d / γ) * γ =
      γ - rateExponent s t d γ * d := by field_simp
  rw [he]
  nlinarith [hh]

theorem high_regime_bias_ordering {s d γ : ℝ} (hd : 0 < d) (hγ : 0 < γ)
    (hhigh : smoothnessThreshold d γ ≤ s) :
    γ / (2 * γ + d) ≤ 2 * s / d := by
  have hh := (div_le_iff₀ (show 0 < 2 * (2 * γ + d) by positivity)).mp hhigh
  apply (div_le_div_iff₀ (show 0 < 2 * γ + d by positivity) hd).mpr
  nlinarith [hh]

theorem rateExponent_eq_partB (A d γ : ℝ) :
    rateExponent (A / 2) 1 d γ = PartB.rateExponent A d γ := by
  unfold rateExponent rateDenominator PartB.rateExponent PartB.rateDenominator
  congr 1 <;> ring

end CausalLowerbound.UpperBound

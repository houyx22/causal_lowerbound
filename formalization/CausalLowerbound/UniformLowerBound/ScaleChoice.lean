import CausalLowerbound.UniformLowerBound.Rates

/-! Uniform finite-sample calibration and the amplitude comparisons used to
select the two asymmetric Bernoulli constructions. -/
noncomputable section
set_option autoImplicit false
namespace CausalLowerbound.UniformLowerBound

theorem exists_calibrated_scales (A d γ Cbad Cgood : ℝ)
    (hA : 0 < A) (hd : 0 < d) (hγ : 0 < γ)
    (hreg : A * (2 + d / γ) < d) (hCbad : 0 ≤ Cbad) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ x : ℝ, 1 ≤ x →
      Cbad * (x ^ ((componentCutoff A d γ : ℝ) + 1) *
        coarseScale A d γ t x ^ d *
        fineScale A d γ t x ^ ((componentCutoff A d γ : ℝ) * d)) +
      Real.sqrt (Cgood * (x ^ (2 : ℝ) * coarseScale A d γ t x ^ d *
        fineScale A d γ t x ^ (d + 2 * A))) ≤ 1 / 2 := by
  have hD := rateDenominator_pos A d γ hA hd hγ
  have hE : 0 < d + fineRatio A γ * ((componentCutoff A d γ : ℝ) * d) := by
    have hq : 0 ≤ fineRatio A γ := (div_pos hγ hA).le
    positivity
  obtain ⟨t, ht, ht1, hb⟩ := exists_tuning (rateDenominator A d γ)
    (d + fineRatio A γ * ((componentCutoff A d γ : ℝ) * d)) Cbad Cgood 1 hD hE zero_lt_one
  refine ⟨t, ht, ht1, ?_⟩
  intro x hx
  rw [collision_ledger A d γ t x hA hd hγ ht (lt_of_lt_of_le zero_lt_one hx)]
  exact (add_le_add_right (mul_le_mul_of_nonneg_left
    (cluster_ledger_le A d γ t x hA hd hγ hreg ht hx) hCbad) _).trans hb

theorem amplitude_product (α β c ℓ : ℝ) (hℓ : 0 < ℓ) :
    (c * ℓ ^ α) * (c * ℓ ^ β) = c ^ 2 * ℓ ^ (α + β) := by
  rw [Real.rpow_add hℓ]
  ring

theorem amplitude_product_sq_le (α β c ℓ : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hℓ : 0 < ℓ) :
    (c * ℓ ^ α) ^ 2 * (c * ℓ ^ β) ^ 2 ≤ ℓ ^ (2 * (α + β)) := by
  have he : (c * ℓ ^ α) ^ 2 * (c * ℓ ^ β) ^ 2 =
      c ^ 4 * ℓ ^ (2 * (α + β)) := by
    rw [← mul_pow, amplitude_product α β c ℓ hℓ, mul_pow,
      ← Real.rpow_natCast (ℓ ^ (α + β)) 2, ← Real.rpow_mul hℓ.le]
    norm_num
    ring_nf
  rw [he]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hℓ.le _)
    (pow_le_one₀ hc hc1)

theorem amplitude_order (α β c ℓ : ℝ) (hc : 0 ≤ c) (hℓ : 0 < ℓ)
    (hℓ1 : ℓ ≤ 1) (hβα : β ≤ α) : c * ℓ ^ α ≤ c * ℓ ^ β :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hℓ hℓ1 hβα) hc

theorem small_amplitude_fourth_le (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ 4 ≤ a ^ 2 * b ^ 2 := by
  have hb : 0 ≤ b := ha.trans hab
  have hs := sq_le_sq₀ ha hb |>.mpr hab
  nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hs)]

theorem component_amplitude_le (α β c ℓ : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    (c * ℓ ^ α) ^ 2 * (c * ℓ ^ β) ^ 2 +
      (if α ≤ β then (c * ℓ ^ β) ^ 4 else (c * ℓ ^ α) ^ 4) ≤
        2 * ℓ ^ (2 * (α + β)) := by
  have ha : 0 ≤ c * ℓ ^ α := mul_nonneg hc (Real.rpow_nonneg hℓ.le _)
  have hb : 0 ≤ c * ℓ ^ β := mul_nonneg hc (Real.rpow_nonneg hℓ.le _)
  have hp := amplitude_product_sq_le α β c ℓ hc hc1 hℓ
  by_cases h : α ≤ β
  · rw [if_pos h]
    have hh := small_amplitude_fourth_le _ _ hb (amplitude_order β α c ℓ hc hℓ hℓ1 h)
    nlinarith
  · rw [if_neg h]
    have hh := small_amplitude_fourth_le _ _ ha (amplitude_order α β c ℓ hc hℓ hℓ1 (le_of_not_ge h))
    linarith

theorem component_monomial_le (α β c ℓ h x C : ℝ) (d : ℕ)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
    (hh : 0 ≤ h) (hC : 0 ≤ C) :
    (C * ((c * ℓ ^ α) ^ 2 * (c * ℓ ^ β) ^ 2 +
      (if α ≤ β then (c * ℓ ^ β) ^ 4 else (c * ℓ ^ α) ^ 4))) *
      (x ^ 2 * h ^ d * ℓ ^ d) ≤
        (2 * C) * (x ^ (2 : ℝ) * h ^ (d : ℝ) * ℓ ^ ((d : ℝ) + 2 * (α + β))) := by
  calc
    _ ≤ (C * (2 * ℓ ^ (2 * (α + β)))) * (x ^ 2 * h ^ d * ℓ ^ d) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (component_amplitude_le α β c ℓ hc hc1 hℓ hℓ1) hC)
        (by positivity)
    _ = _ := by rw [Real.rpow_add hℓ]; simp only [Real.rpow_natCast, Real.rpow_two]; ring

theorem amplitude_signal (α β d γ c t x : ℝ)
    (hA : 0 < α + β) (hd : 0 < d) (hγ : 0 < γ)
    (hreg : (α + β) * (2 + d / γ) < d) (ht : 0 < t) (ht1 : t ≤ 1) (hx : 1 ≤ x) :
    (c * fineScale (α + β) d γ t x ^ α) *
      (c * fineScale (α + β) d γ t x ^ β) =
        (c ^ 2 * t ^ γ) * x ^ (-rateExponent (α + β) d γ) := by
  have hs := scales_valid (α + β) d γ t x hA hd hγ hreg ht ht1 hx
  rw [amplitude_product α β c _ hs.1, hs.2.2.2.2,
    signal_ledger (α + β) d γ t x ht (lt_of_lt_of_le zero_lt_one hx)]
  ring

theorem rateExponent_eq_balanced (A d γ : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) :
    rateExponent A d γ = (2 * A) / (d + 2 * A + d * A / γ) := by
  rw [rateExponent_eq A d γ hA hd hγ]
  have hleft : 1 + d / (2 * γ) + d / (2 * A) ≠ 0 := by positivity
  have hright : d + 2 * A + d * A / γ ≠ 0 := by positivity
  field_simp
  ring

end CausalLowerbound.UniformLowerBound

import CausalLowerbound.PartB.BalancedScales
import CausalLowerbound.PartB.LogarithmicScale

/-! The exponent choice and all three global rate ledgers in Part B.
Here s₁ = 1. We use the permitted concrete choice c = 1/(2 A),
which makes the small-epsilon ordering particularly transparent. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace CausalLowerbound.PartB

def rateDenominator (d γ : ℝ) : ℝ := d + 4 + 2 * d / γ
def rateExponent (A d γ : ℝ) : ℝ := (A + 2) / rateDenominator d γ
def carrierExponent (A d ε : ℝ) : ℝ := 1 / d + ε / (2 * A)
def jitterExponent (A d γ ε : ℝ) : ℝ :=
  (rateExponent A d γ + ε - carrierExponent A d ε * A) / 2
def matchingOrder (d γ z b : ℝ) : ℕ := max 2 (1 + ⌊max (1 - z * d / γ) 0 / b⌋₊)

theorem rateDenominator_pos (d γ : ℝ) (hd : 0 < d) (hγ : 0 < γ) : 0 < rateDenominator d γ := by
  dsimp [rateDenominator]
  positivity

theorem rate_ordering (A d γ : ℝ) (hA : 0 < A) (hd : 0 < d) (hγ : 0 < γ)
    (hreg : A * (2 + d / γ) < d) :
    A < γ ∧ A / d < rateExponent A d γ ∧ rateExponent A d γ < γ / d ∧
      0 < rateExponent A d γ ∧ rateExponent A d γ < 1 := by
  have hD := rateDenominator_pos d γ hd hγ
  have hreg' : A * (2 * γ + d) < d * γ := by
    have h := (mul_lt_mul_right hγ).mpr hreg
    field_simp at h
    nlinarith
  have hAg : A < γ := by
    nlinarith [mul_pos hA hγ]
  have hAd : 2 * A < d := by
    nlinarith [div_pos hd hγ]
  have hDg : rateDenominator d γ * γ = d * γ + 4 * γ + 2 * d := by
    unfold rateDenominator
    field_simp
    ring
  refine ⟨hAg, ?_, ?_, div_pos (by linarith) hD, ?_⟩
  · apply (div_lt_div_iff₀ hd hD).mpr
    dsimp [rateDenominator]
    simp only [div_eq_mul_inv] at hreg ⊢
    nlinarith [hreg]
  · apply (div_lt_div_iff₀ hD hd).mpr
    nlinarith [mul_pos hd (sub_pos.mpr hAg)]
  · apply (div_lt_one hD).mpr
    dsimp [rateDenominator]
    have hdiv := div_pos hd hγ
    simp only [div_eq_mul_inv] at hdiv ⊢
    nlinarith

theorem concrete_scale_exponents (A d γ ε : ℝ) (hA : 0 < A) (hd : 0 < d) (hγ : 0 < γ)
    (hreg : A * (2 + d / γ) < d) (hε : 0 < ε)
    (hεsmall : ε < γ / d - rateExponent A d γ) :
    0 < rateExponent A d γ + ε ∧
      (rateExponent A d γ + ε) / γ < carrierExponent A d ε ∧
      0 < jitterExponent A d γ ε := by
  have ho := rate_ordering A d γ hA hd hγ hreg
  have hc : carrierExponent A d ε * A = A / d + ε / 2 := by
    dsimp [carrierExponent]
    field_simp
    ring
  refine ⟨add_pos ho.2.2.2.1 hε, ?_, ?_⟩
  · have hz : rateExponent A d γ + ε < γ / d := by linarith
    have hz' : (rateExponent A d γ + ε) / γ < 1 / d := by
      apply (div_lt_iff₀ hγ).mpr
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hz
    exact hz'.trans (by dsimp [carrierExponent]; linarith [div_pos hε (mul_pos two_pos hA)])
  · dsimp [jitterExponent]
    rw [hc]
    linarith [ho.2.1]

theorem matchingOrder_ge_two (d γ z b : ℝ) : 2 ≤ matchingOrder d γ z b := le_max_left _ _

theorem matchingOrder_exponent_neg (d γ z b : ℝ) (hb : 0 < b) :
    1 - z * d / γ - b * matchingOrder d γ z b < 0 := by
  have hf : max (1 - z * d / γ) 0 / b < (matchingOrder d γ z b : ℝ) := by
    have h := Nat.lt_floor_add_one (max (1 - z * d / γ) 0 / b)
    have hm : 1 + ⌊max (1 - z * d / γ) 0 / b⌋₊ ≤ matchingOrder d γ z b := le_max_right _ _
    have hm' : (⌊max (1 - z * d / γ) 0 / b⌋₊ : ℝ) + 1 ≤ (matchingOrder d γ z b : ℝ) := by
      exact_mod_cast (show ⌊max (1 - z * d / γ) 0 / b⌋₊ + 1 ≤ matchingOrder d γ z b by omega)
    exact h.trans_le hm'
  have h := (div_lt_iff₀ hb).mp hf
  nlinarith [le_max_left (1 - z * d / γ) 0]

/-- The identities are algebraic consequences of the rate, not input assumptions. -/
theorem rate_exponent_ledgers (A d γ ε : ℝ) (hA : A ≠ 0) (hd : d ≠ 0) (hγ : γ ≠ 0)
    (hD : rateDenominator d γ ≠ 0) :
    1 - (rateExponent A d γ + ε) * d / γ - d * jitterExponent A d γ ε -
        2 * (rateExponent A d γ + ε) = -ε * (rateDenominator d γ - d / 2) / 2 ∧
    2 - (rateExponent A d γ + ε) * d / γ -
        d * (jitterExponent A d γ ε + carrierExponent A d ε) -
        2 * (rateExponent A d γ + ε) =
      -ε * (rateDenominator d γ - d / 2) / 2 - d * ε / (2 * A) := by
  have hρ : rateExponent A d γ * rateDenominator d γ = A + 2 := div_mul_cancel₀ _ hD
  have hξ : d * carrierExponent A d ε * A = A + d * ε / 2 := by
    dsimp [carrierExponent]
    field_simp
    ring
  have hξ' : d * carrierExponent A d ε = 1 + d * ε / (2 * A) := by
    dsimp [carrierExponent]
    field_simp
    ring
  have hfirst : 1 - (rateExponent A d γ + ε) * d / γ - d * jitterExponent A d γ ε -
      2 * (rateExponent A d γ + ε) = -ε * (rateDenominator d γ - d / 2) / 2 := by
    dsimp [jitterExponent, rateDenominator] at hρ ⊢
    linear_combination -1 / 2 * hρ + 1 / 2 * hξ
  refine ⟨hfirst, ?_⟩
  linear_combination hfirst - hξ'

theorem rate_ledger_exponents_negative (A d γ ε : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hε : 0 < ε) :
    -ε * (rateDenominator d γ - d / 2) / 2 < 0 ∧
      -ε * (rateDenominator d γ - d / 2) / 2 - d * ε / (2 * A) < 0 := by
  have hh : 0 < rateDenominator d γ - d / 2 := by
    dsimp [rateDenominator]
    have hh := div_pos hd hγ
    simp only [div_eq_mul_inv] at hh ⊢
    nlinarith
  have he : -ε * (rateDenominator d γ - d / 2) / 2 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hε) hh) two_pos
  exact ⟨he, by linarith [div_pos (mul_pos hd hε) (mul_pos two_pos hA)]⟩

theorem polynomial_log_tendsto (a B : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-a) * logScale (n + 1) ^ B) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  by_cases hB : 0 ≤ B
  · simpa only [logarithmicThreshold, polynomialAmplitude, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (logarithmicThreshold_tendsto a B ha hB).comp hx
  · have hpow := (tendsto_rpow_neg_atTop ha).comp hx
    have hn1 (n : ℕ) : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hnonneg (n : ℕ) : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-a) * logScale (n + 1) ^ B :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (logScale_pos (hn1 n)).le _)
    apply squeeze_zero' (Filter.Eventually.of_forall hnonneg) _ hpow
    filter_upwards [] with n
    have h := Real.rpow_le_one_of_one_le_of_nonpos (logScale_one_le (hn1 n))
      (le_of_not_ge hB)
    simpa only [Nat.cast_add, Nat.cast_one, mul_one] using
      mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) (-a))

end CausalLowerbound.PartB

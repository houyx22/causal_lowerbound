import CausalLowerbound.PartB.RateRegime

/-! Mixed-smoothness rate exponents. The effective smoothness `s` is left
general; Part C will use `(1 + min α β) / 2`. The carrier scale uses the
same concrete choice `c = 1 / (2 A)` as Part B. -/
noncomputable section
set_option autoImplicit false
namespace CausalLowerbound.PartC

def effectiveSmoothness (α β : ℝ) : ℝ := (1 + min α β) / 2
def rateDenominator (d γ s : ℝ) : ℝ := d + 4 * s + 2 * d * s / γ
def rateExponent (A d γ s : ℝ) : ℝ := (A + 2 * s) / rateDenominator d γ s
abbrev carrierExponent := PartB.carrierExponent
def jitterExponent (A d γ s ε : ℝ) : ℝ :=
  (rateExponent A d γ s + ε - carrierExponent A d ε * A) / (2 * s)
def rateMargin (d γ s ε : ℝ) : ℝ :=
  ε * (rateDenominator d γ s - d / 2) / (2 * s)

theorem effectiveSmoothness_pos (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    0 < effectiveSmoothness α β := by
  unfold effectiveSmoothness
  positivity

theorem effectiveSmoothness_le_one (α β : ℝ) (h : min α β ≤ 1) :
    effectiveSmoothness α β ≤ 1 := by
  unfold effectiveSmoothness
  linarith

theorem rateDenominator_pos (d γ s : ℝ) (hd : 0 < d) (hγ : 0 < γ) (hs : 0 < s) :
    0 < rateDenominator d γ s := by
  unfold rateDenominator
  positivity

theorem rateExponent_rescale (A d γ s : ℝ) (hγ : γ ≠ 0) (hs : s ≠ 0) :
    rateExponent A d γ s = PartB.rateExponent (A / s) (d / s) (γ / s) := by
  have hnum : A / s + 2 = (A + 2 * s) / s := by field_simp
  have hden : PartB.rateDenominator (d / s) (γ / s) = rateDenominator d γ s / s := by
    unfold PartB.rateDenominator rateDenominator
    field_simp <;> ring_nf <;> simp
  unfold rateExponent PartB.rateExponent
  rw [hnum, hden, div_div_div_cancel_right₀ hs]

theorem rate_ordering (A d γ s : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hs : 0 < s) (hreg : A * (2 + d / γ) < d) :
    A < γ ∧ A / d < rateExponent A d γ s ∧ rateExponent A d γ s < γ / d ∧
      0 < rateExponent A d γ s ∧ rateExponent A d γ s < 1 := by
  have hreg' : A / s * (2 + (d / s) / (γ / s)) < d / s := by
    rw [div_div_div_cancel_right₀ hs.ne']
    simpa only [div_mul_eq_mul_div] using (div_lt_div_of_pos_right hreg hs)
  have ho := PartB.rate_ordering (A / s) (d / s) (γ / s)
    (div_pos hA hs) (div_pos hd hs) (div_pos hγ hs) hreg'
  rw [← rateExponent_rescale A d γ s hγ.ne' hs.ne',
    div_div_div_cancel_right₀ hs.ne', div_div_div_cancel_right₀ hs.ne'] at ho
  exact ⟨(div_lt_div_iff_of_pos_right hs).mp ho.1, ho.2⟩

theorem concrete_scale_exponents (A d γ s ε : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hs : 0 < s) (hreg : A * (2 + d / γ) < d) (hε : 0 < ε)
    (hεsmall : ε < γ / d - rateExponent A d γ s) :
    0 < rateExponent A d γ s + ε ∧
      (rateExponent A d γ s + ε) / γ < carrierExponent A d ε ∧
      0 < jitterExponent A d γ s ε := by
  have ho := rate_ordering A d γ s hA hd hγ hs hreg
  have hc : carrierExponent A d ε * A = A / d + ε / 2 := by
    unfold carrierExponent PartB.carrierExponent
    field_simp
    ring
  refine ⟨add_pos ho.2.2.2.1 hε, ?_, ?_⟩
  · have hz : rateExponent A d γ s + ε < γ / d := by linarith
    have hz' : (rateExponent A d γ s + ε) / γ < 1 / d := by
      apply (div_lt_iff₀ hγ).mpr
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hz
    exact hz'.trans (by
      unfold carrierExponent PartB.carrierExponent
      linarith [div_pos hε (mul_pos two_pos hA)])
  · unfold jitterExponent
    rw [hc]
    exact div_pos (by linarith [ho.2.1]) (by positivity)

theorem rateMargin_pos (d γ s ε : ℝ) (hd : 0 < d) (hγ : 0 < γ)
    (hs : 0 < s) (hε : 0 < ε) : 0 < rateMargin d γ s ε := by
  have hD : 0 < rateDenominator d γ s - d / 2 := by
    unfold rateDenominator
    linarith [div_pos (mul_pos (mul_pos two_pos hd) hs) hγ]
  exact div_pos (mul_pos hε hD) (by positivity)

theorem rate_exponent_ledgers (A d γ s ε : ℝ) (hA : A ≠ 0) (hd : d ≠ 0)
    (hγ : γ ≠ 0) (hs : s ≠ 0) (hD : rateDenominator d γ s ≠ 0) :
    1 - (rateExponent A d γ s + ε) * d / γ - d * jitterExponent A d γ s ε -
        2 * (rateExponent A d γ s + ε) = -rateMargin d γ s ε ∧
      2 - (rateExponent A d γ s + ε) * d / γ -
        d * (jitterExponent A d γ s ε + carrierExponent A d ε) -
        2 * (rateExponent A d γ s + ε) = -rateMargin d γ s ε - d * ε / (2 * A) := by
  have hρ : rateExponent A d γ s * rateDenominator d γ s = A + 2 * s :=
    div_mul_cancel₀ _ hD
  have hξ : d * carrierExponent A d ε * A = A + d * ε / 2 := by
    unfold carrierExponent PartB.carrierExponent
    field_simp
    ring
  have hξ' : d * carrierExponent A d ε = 1 + d * ε / (2 * A) := by
    unfold carrierExponent PartB.carrierExponent
    field_simp
    ring
  have hfirst : 1 - (rateExponent A d γ s + ε) * d / γ -
      d * jitterExponent A d γ s ε - 2 * (rateExponent A d γ s + ε) =
        -rateMargin d γ s ε := by
    have hp : 2 * s * jitterExponent A d γ s ε =
        rateExponent A d γ s + ε - carrierExponent A d ε * A := by
      unfold jitterExponent
      field_simp
    unfold rateMargin
    unfold rateDenominator at hρ ⊢
    linear_combination (norm := skip) -(1 / (2 * s)) * hρ +
      (1 / (2 * s)) * hξ - (d / (2 * s)) * hp
    field_simp
    ring
  refine ⟨hfirst, ?_⟩
  linear_combination hfirst - hξ'

theorem rate_ledger_exponents_negative (A d γ s ε : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hs : 0 < s) (hε : 0 < ε) :
    -rateMargin d γ s ε < 0 ∧ -rateMargin d γ s ε - d * ε / (2 * A) < 0 := by
  have hm := rateMargin_pos d γ s ε hd hγ hs hε
  exact ⟨by linarith, by linarith [div_pos (mul_pos hd hε) (by positivity : 0 < 2 * A)]⟩

end CausalLowerbound.PartC

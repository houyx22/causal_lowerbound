import CausalLowerbound.UpperBound.BandwidthAdmissibility

/-! The two variance powers and the bias powers evaluated at polynomial
bandwidths.  These numerical bounds will be combined with the actual risk
theorem; no stochastic or geometric conclusion is assumed here. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

theorem stencilVarianceTerm_mono {h ℓ η ζ : ℝ} (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ)
    (hη : 0 ≤ η) (hηζ : η ≤ ζ) :
    stencilVarianceTerm (d := d) h ℓ η ≤ stencilVarianceTerm (d := d) h ℓ ζ := by
  unfold stencilVarianceTerm
  exact add_le_add (div_le_div_of_nonneg_right hηζ (by positivity))
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hη hηζ 2) (by positivity))

theorem stencilVarianceTerm_polynomial (a b H : ℝ) (n : ℕ) :
    stencilVarianceTerm (d := d) (polynomialBandwidth a n) (polynomialBandwidth b n)
      (H * polynomialBandwidth 1 n) = (4 : ℝ) ^ Fintype.card d *
        (H * polynomialBandwidth (1 - a * Fintype.card d) n +
          H ^ 2 * polynomialBandwidth (2 - (a + b) * Fintype.card d) n) := by
  have ha := (polynomialBandwidth_pos a n).ne'
  have hb := (polynomialBandwidth_pos b n).ne'
  calc
    _ = (4 : ℝ) ^ Fintype.card d *
        (H * (polynomialBandwidth 1 n / polynomialBandwidth a n ^ Fintype.card d) +
          H ^ 2 * (polynomialBandwidth 1 n ^ 2 /
            (polynomialBandwidth a n ^ Fintype.card d * polynomialBandwidth b n ^ Fintype.card d))) := by
      unfold stencilVarianceTerm
      rw [div_pow]
      field_simp
      ring
    _ = _ := by
      simp only [polynomialBandwidth_pow, one_mul, polynomialBandwidth_mul, polynomialBandwidth_div]
      congr 3
      congr 1
      ring

theorem stencilVarianceTerm_polynomial_le {a b H η ρ : ℝ} (n : ℕ)
    (hH : 0 ≤ H) (hη : 0 ≤ η) (hηH : η ≤ H * polynomialBandwidth 1 n)
    (h₁ : 2 * ρ ≤ 1 - a * Fintype.card d)
    (h₂ : 2 * ρ ≤ 2 - (a + b) * Fintype.card d) :
    stencilVarianceTerm (d := d) (polynomialBandwidth a n) (polynomialBandwidth b n) η ≤
      ((4 : ℝ) ^ Fintype.card d * (H + H ^ 2)) * polynomialBandwidth (2 * ρ) n := by
  apply (stencilVarianceTerm_mono (polynomialBandwidth_pos _ _).le
    (polynomialBandwidth_pos _ _).le hη hηH).trans
  rw [stencilVarianceTerm_polynomial]
  calc
    _ ≤ (4 : ℝ) ^ Fintype.card d *
        (H * polynomialBandwidth (2 * ρ) n + H ^ 2 * polynomialBandwidth (2 * ρ) n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left (polynomialBandwidth_antitone h₁ n) hH)
        (mul_le_mul_of_nonneg_left (polynomialBandwidth_antitone h₂ n) (sq_nonneg _))
    _ = _ := by ring

theorem sqrt_stencilVarianceTerm_polynomial_le {a b H η ρ : ℝ} (n : ℕ)
    (hH : 0 ≤ H) (hη : 0 ≤ η) (hηH : η ≤ H * polynomialBandwidth 1 n)
    (h₁ : 2 * ρ ≤ 1 - a * Fintype.card d)
    (h₂ : 2 * ρ ≤ 2 - (a + b) * Fintype.card d) :
    Real.sqrt (stencilVarianceTerm (d := d) (polynomialBandwidth a n) (polynomialBandwidth b n) η) ≤
      Real.sqrt ((4 : ℝ) ^ Fintype.card d * (H + H ^ 2)) * polynomialBandwidth ρ n := by
  have he := Real.sqrt_le_sqrt (stencilVarianceTerm_polynomial_le n hH hη hηH h₁ h₂)
  have hs : polynomialBandwidth (2 * ρ) n = polynomialBandwidth ρ n ^ 2 := by
    rw [polynomialBandwidth_pow]
    congr 1
    push_cast
    ring
  simpa only [hs, Real.sqrt_mul (by positivity : 0 ≤ (4 : ℝ) ^ Fintype.card d * (H + H ^ 2)),
    Real.sqrt_sq (polynomialBandwidth_pos ρ n).le] using he

theorem twoScaleModulus_product_polynomial (α β b c : ℝ) (n : ℕ) :
    twoScaleModulus α (polynomialBandwidth b n) (polynomialBandwidth c n) *
      twoScaleModulus β (polynomialBandwidth b n) (polynomialBandwidth c n) =
      polynomialBandwidth (b * (min α 1 + min β 1) + c * (α + β - (min α 1 + min β 1))) n := by
  rw [twoScaleModulus_product α β _ _ (polynomialBandwidth_pos _ _) (polynomialBandwidth_pos _ _),
    polynomialBandwidth_rpow, polynomialBandwidth_rpow, polynomialBandwidth_mul]

theorem polynomial_master_terms_le {α β γ a b c H η ρ : ℝ} (n : ℕ)
    (hH : 0 ≤ H) (hη : 0 ≤ η) (hηH : η ≤ H * polynomialBandwidth 1 n)
    (hγ : ρ ≤ a * γ)
    (hαβ : ρ ≤ b * (min α 1 + min β 1) + c * (α + β - (min α 1 + min β 1)))
    (h₁ : 2 * ρ ≤ 1 - a * Fintype.card d)
    (h₂ : 2 * ρ ≤ 2 - (a + b) * Fintype.card d) :
    polynomialBandwidth a n ^ γ +
      twoScaleModulus α (polynomialBandwidth b n) (polynomialBandwidth c n) *
        twoScaleModulus β (polynomialBandwidth b n) (polynomialBandwidth c n) +
          Real.sqrt (stencilVarianceTerm (d := d) (polynomialBandwidth a n) (polynomialBandwidth b n) η) ≤
      (2 + Real.sqrt ((4 : ℝ) ^ Fintype.card d * (H + H ^ 2))) * polynomialBandwidth ρ n := by
  rw [polynomialBandwidth_rpow, twoScaleModulus_product_polynomial]
  have he := add_le_add (add_le_add (polynomialBandwidth_antitone hγ n) (polynomialBandwidth_antitone hαβ n))
    (sqrt_stencilVarianceTerm_polynomial_le n hH hη hηH h₁ h₂)
  convert he using 1 <;> ring

end CausalLowerbound.UpperBound

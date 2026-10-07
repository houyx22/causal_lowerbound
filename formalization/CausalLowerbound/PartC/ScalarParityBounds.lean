import CausalLowerbound.PartC.SharedSignParity

/-! Parity bounds for general coefficients close to a sign-independent
baseline. This includes all four normalized coefficients of a cubic
outcome likelihood, including coefficients whose baseline is zero. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]

theorem odd_weighted_scalar_bound (F g : (J → Bool) → ℝ)
    (hodd : ∀ ζ, F (Walsh.flip ζ) = -F ζ)
    (M L rough base : ℝ) (hM : 0 ≤ M) (hF : ∀ ζ, |F ζ| ≤ M)
    (hg : ∀ ζ, |g ζ - base| ≤ L * rough) :
    |independentSigns.expect (fun ζ => F ζ * g ζ)| ≤ M * (L * rough) := by
  have hz := independentSigns_expect_odd F hodd
  have he : independentSigns.expect (fun ζ => F ζ * g ζ) =
      independentSigns.expect (fun ζ => F ζ * (g ζ - base)) := by
    simp only [mul_sub, FiniteLaw.expect_sub, FiniteLaw.expect_mul_const, hz, zero_mul, sub_zero]
  rw [he]
  apply FiniteLaw.abs_expect_le_bound
  intro ζ
  rw [abs_mul]
  exact mul_le_mul (hF ζ) (hg ζ) (abs_nonneg _) hM

theorem parity_weighted_scalar_shift_bound (e : ℕ) (he : 0 < e) (F : (J → Bool) → ℝ)
    (hparity : ∀ ζ, F (Walsh.flip ζ) = (-1) ^ e * F ζ) (g : (J → Bool) → ℝ)
    (M L shift rough base : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hshift : 0 ≤ shift) (hrough : 0 ≤ rough) (hr1 : rough ≤ 1) (hsr : shift ≤ rough)
    (hF : ∀ ζ, |F ζ| ≤ M) (hg : ∀ ζ, |g ζ| ≤ L)
    (hgb : ∀ ζ, |g ζ - base| ≤ L * rough) :
    |independentSigns.expect (fun ζ => shift ^ e * F ζ * g ζ)| ≤ M * L * (shift * rough) := by
  have hexp : independentSigns.expect (fun ζ => shift ^ e * F ζ * g ζ) =
      shift ^ e * independentSigns.expect (fun ζ => F ζ * g ζ) := by
    simp only [mul_assoc, FiniteLaw.expect_mul]
  rw [hexp, abs_mul, abs_of_nonneg (pow_nonneg hshift e)]
  by_cases he1 : e = 1
  · subst e
    have hodd : ∀ ζ, F (Walsh.flip ζ) = -F ζ := by
      intro ζ
      simpa only [pow_one, neg_one_mul] using hparity ζ
    rw [pow_one]
    calc
      _ ≤ shift * (M * (L * rough)) := mul_le_mul_of_nonneg_left
        (odd_weighted_scalar_bound F g hodd M L rough base hM hF hgb) hshift
      _ = _ := by ring
  · have he2 : 2 ≤ e := by omega
    have hp : shift ^ e ≤ shift * rough := by
      calc
        _ ≤ shift ^ 2 := pow_le_pow_of_le_one hshift (hsr.trans hr1) he2
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsr hshift]
    have hb : |independentSigns.expect (fun ζ => F ζ * g ζ)| ≤ M * L := by
      apply FiniteLaw.abs_expect_le_bound
      intro ζ
      rw [abs_mul]
      exact mul_le_mul (hF ζ) (hg ζ) (abs_nonneg _) hM
    calc
      _ ≤ shift ^ e * (M * L) := mul_le_mul_of_nonneg_left hb (pow_nonneg hshift e)
      _ ≤ (shift * rough) * (M * L) := mul_le_mul_of_nonneg_right hp (mul_nonneg hM hL)
      _ = _ := by ring

theorem bounded_scalar_product (f : I → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ i, |f i| ≤ C) :
    |∏ i, f i| ≤ C ^ Fintype.card I := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i : I, C := Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hf i)
    _ = _ := by simp

theorem scalar_product_baseline_bound (g : I → (J → Bool) → ℝ) (base : I → ℝ)
    (C rough : ℝ) (hC : 1 ≤ C) (hg : ∀ i ζ, |g i ζ| ≤ C) (hb : ∀ i, |base i| ≤ C)
    (hgb : ∀ i ζ, |g i ζ - base i| ≤ C * rough) (ζ : J → Bool) :
    |(∏ i, g i ζ) - ∏ i, base i| ≤ C ^ Fintype.card I * (Fintype.card I : ℝ) * C * rough := by
  have hp := abs_prod_sub_prod_le_bounded Finset.univ (fun i => g i ζ) base C hC
    (fun i _ => hg i ζ) (fun i _ => hb i)
  apply hp.trans
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hgb i ζ))
    (pow_nonneg (zero_le_one.trans hC) (Fintype.card I))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hs

theorem parity_weighted_scalar_product_shift_bound (e : ℕ) (he : 0 < e) (F : (J → Bool) → ℝ)
    (hparity : ∀ ζ, F (Walsh.flip ζ) = (-1) ^ e * F ζ)
    (g : I → (J → Bool) → ℝ) (base : I → ℝ) (M C shift rough : ℝ)
    (hM : 0 ≤ M) (hC : 1 ≤ C) (hshift : 0 ≤ shift) (hrough : 0 ≤ rough)
    (hr1 : rough ≤ 1) (hsr : shift ≤ rough) (hF : ∀ ζ, |F ζ| ≤ M)
    (hg : ∀ i ζ, |g i ζ| ≤ C) (hb : ∀ i, |base i| ≤ C)
    (hgb : ∀ i ζ, |g i ζ - base i| ≤ C * rough) :
    |independentSigns.expect (fun ζ => shift ^ e * F ζ * ∏ i, g i ζ)| ≤
      M * (C ^ Fintype.card I * ((Fintype.card I : ℝ) * C + 1)) * (shift * rough) := by
  have hC0 := zero_le_one.trans hC
  have hCpow := pow_nonneg hC0 (Fintype.card I)
  have hn : 0 ≤ (Fintype.card I : ℝ) * C := mul_nonneg (Nat.cast_nonneg _) hC0
  apply parity_weighted_scalar_shift_bound e he F hparity (fun ζ => ∏ i, g i ζ)
    M (C ^ Fintype.card I * ((Fintype.card I : ℝ) * C + 1)) shift rough (∏ i, base i)
    hM (mul_nonneg hCpow (by linarith)) hshift hrough hr1 hsr hF
  · intro ζ
    exact (bounded_scalar_product (fun i => g i ζ) C hC0 (fun i => hg i ζ)).trans
      (le_mul_of_one_le_right hCpow (by linarith))
  · intro ζ
    have hp := scalar_product_baseline_bound g base C rough hC hg hb hgb ζ
    apply hp.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (a := (Fintype.card I : ℝ) * C) zero_le_one) hCpow) hrough
    simpa only [mul_assoc] using hh

end CausalLowerbound.PartC

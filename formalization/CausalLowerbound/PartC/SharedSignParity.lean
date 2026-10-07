import CausalLowerbound.PartC.WalshParity
import CausalLowerbound.FiniteProductBounds

/-! Quantitative parity cancellation under the original shared sign law.
An odd coefficient forces a rough-amplitude factor from an affine
likelihood product. Terms with at least two shifts instead use the
shift-square bound. No independence between physical sites is assumed. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I]

theorem independentSigns_expect_flip (F : (J → Bool) → ℝ) :
    independentSigns.expect (fun ζ => F (Walsh.flip ζ)) = independentSigns.expect F := by
  let e : (J → Bool) ≃ (J → Bool) :=
    ⟨Walsh.flip, Walsh.flip, Walsh.flip_flip, Walsh.flip_flip⟩
  simp only [FiniteLaw.expect, independentSigns, FiniteLaw.independent, rademacher, Finset.prod_const]
  exact e.sum_comp (fun ζ => (1 / 2 : ℝ) ^ Fintype.card J * F ζ)

theorem independentSigns_expect_odd (F : (J → Bool) → ℝ)
    (hF : ∀ ζ, F (Walsh.flip ζ) = -F ζ) : independentSigns.expect F = 0 := by
  have he := independentSigns_expect_flip F
  simp only [hF, FiniteLaw.expect, mul_neg, Finset.sum_neg_distrib] at he
  change (∑ ζ, independentSigns.weight ζ * F ζ) = 0
  linarith

theorem affine_rough_product_bound (f : I → (J → Bool) → ℝ) (small : ℝ) (hs : small ≤ 1)
    (hf : ∀ i ζ, |f i ζ| ≤ small) (ζ : J → Bool) :
    |∏ i, (1 + f i ζ)| ≤ (2 : ℝ) ^ Fintype.card I := by
  calc
    _ = ∏ i, |1 + f i ζ| := Finset.abs_prod _ _
    _ ≤ ∏ _i : I, (2 : ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro i _
      calc
        _ ≤ |(1 : ℝ)| + |f i ζ| := abs_add _ _
        _ ≤ 1 + 1 := add_le_add (by norm_num) ((hf i ζ).trans hs)
        _ = 2 := by norm_num
    _ = _ := by simp

theorem affine_rough_product_increment_bound (f : I → (J → Bool) → ℝ)
    (small : ℝ) (hs : small ≤ 1) (hf : ∀ i ζ, |f i ζ| ≤ small) (ζ : J → Bool) :
    |(∏ i, (1 + f i ζ)) - 1| ≤ (2 : ℝ) ^ Fintype.card I * Fintype.card I * small := by
  have hb (i : I) : |1 + f i ζ| ≤ 2 := by
    calc
      _ ≤ |(1 : ℝ)| + |f i ζ| := abs_add _ _
      _ ≤ 1 + 1 := add_le_add (by norm_num) ((hf i ζ).trans hs)
      _ = 2 := by norm_num
  have he := abs_prod_sub_prod_le_bounded Finset.univ (fun i => 1 + f i ζ) (fun _ : I => 1)
    2 (by norm_num) (fun i _ => hb i) (by intro i _; norm_num)
  simp only [Finset.prod_const_one, add_sub_cancel_left, Finset.card_univ] at he
  apply he.trans
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hf i ζ))
    (show 0 ≤ (2 : ℝ) ^ Fintype.card I by positivity)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hh

theorem odd_weighted_rough_product_bound (F : (J → Bool) → ℝ)
    (hodd : ∀ ζ, F (Walsh.flip ζ) = -F ζ)
    (f : I → (J → Bool) → ℝ) (M small : ℝ) (hM : 0 ≤ M) (hs : small ≤ 1)
    (hF : ∀ ζ, |F ζ| ≤ M) (hf : ∀ i ζ, |f i ζ| ≤ small) :
    |independentSigns.expect (fun ζ => F ζ * ∏ i, (1 + f i ζ))| ≤
      M * (2 : ℝ) ^ Fintype.card I * Fintype.card I * small := by
  have hz := independentSigns_expect_odd F hodd
  have he : independentSigns.expect (fun ζ => F ζ * ∏ i, (1 + f i ζ)) =
      independentSigns.expect (fun ζ => F ζ * ((∏ i, (1 + f i ζ)) - 1)) := by
    simp only [mul_sub, mul_one, FiniteLaw.expect_sub, hz, sub_zero]
  rw [he]
  apply FiniteLaw.abs_expect_le_bound
  intro ζ
  rw [abs_mul]
  calc
    _ ≤ M * ((2 : ℝ) ^ Fintype.card I * Fintype.card I * small) :=
      mul_le_mul (hF ζ) (affine_rough_product_increment_bound f small hs hf ζ) (abs_nonneg _) hM
    _ = _ := by ring

theorem parity_weighted_shift_bound (e : ℕ) (he : 0 < e) (F : (J → Bool) → ℝ)
    (hparity : ∀ ζ, F (Walsh.flip ζ) = (-1) ^ e * F ζ)
    (f : I → (J → Bool) → ℝ) (M shift rough : ℝ)
    (hM : 0 ≤ M) (hshift : 0 ≤ shift) (hrough : 0 ≤ rough) (hr1 : rough ≤ 1)
    (hsr : shift ≤ rough) (hF : ∀ ζ, |F ζ| ≤ M) (hf : ∀ i ζ, |f i ζ| ≤ rough) :
    |independentSigns.expect (fun ζ => shift ^ e * F ζ * ∏ i, (1 + f i ζ))| ≤
      M * (2 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) + 1) * (shift * rough) := by
  have hm : 0 ≤ M * (2 : ℝ) ^ Fintype.card I := mul_nonneg hM (by positivity)
  have hsr0 : 0 ≤ shift * rough := mul_nonneg hshift hrough
  have hexp : independentSigns.expect (fun ζ => shift ^ e * F ζ * ∏ i, (1 + f i ζ)) =
      shift ^ e * independentSigns.expect (fun ζ => F ζ * ∏ i, (1 + f i ζ)) := by
    simp only [mul_assoc, FiniteLaw.expect_mul]
  rw [hexp, abs_mul, abs_of_nonneg (pow_nonneg hshift e)]
  by_cases he1 : e = 1
  · subst e
    have hodd : ∀ ζ, F (Walsh.flip ζ) = -F ζ := by
      intro ζ
      simpa only [pow_one, neg_one_mul] using hparity ζ
    rw [pow_one]
    calc
      _ ≤ shift * (M * (2 : ℝ) ^ Fintype.card I * Fintype.card I * rough) :=
        mul_le_mul_of_nonneg_left (odd_weighted_rough_product_bound F hodd f M rough hM hr1 hF hf) hshift
      _ = M * (2 : ℝ) ^ Fintype.card I * Fintype.card I * (shift * rough) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hm) hsr0
  · have he2 : 2 ≤ e := by omega
    have hp : shift ^ e ≤ shift * rough := by
      calc
        _ ≤ shift ^ 2 := pow_le_pow_of_le_one hshift (hsr.trans hr1) he2
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsr hshift]
    have hb : |independentSigns.expect (fun ζ => F ζ * ∏ i, (1 + f i ζ))| ≤
        M * (2 : ℝ) ^ Fintype.card I := by
      apply FiniteLaw.abs_expect_le_bound
      intro ζ
      rw [abs_mul]
      exact mul_le_mul (hF ζ) (affine_rough_product_bound f rough hr1 hf ζ) (abs_nonneg _) hM
    calc
      _ ≤ shift ^ e * (M * (2 : ℝ) ^ Fintype.card I) := mul_le_mul_of_nonneg_left hb (pow_nonneg hshift e)
      _ ≤ (shift * rough) * (M * (2 : ℝ) ^ Fintype.card I) := mul_le_mul_of_nonneg_right hp hm
      _ = M * (2 : ℝ) ^ Fintype.card I * 1 * (shift * rough) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (by have := Nat.cast_nonneg (α := ℝ) (Fintype.card I); linarith) hm) hsr0

end CausalLowerbound.PartC

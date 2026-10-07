import CausalLowerbound.PartC.ScalarResamplingParity

/-! Compare two products after one shared resampling, retaining the
shift-times-rough saving for general scalar likelihood coefficients. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB
variable {J K P : Type*} [Fintype J] [DecidableEq J] [Fintype K] [Fintype P]

theorem resampled_product_comparison_scalar_shift_bound
    (T : Finset J) (e : K → ℕ) (he : 0 < ∑ k, e k)
    (F G : K → (J → Bool) → (J → Bool) → ℝ)
    (hFp : ∀ k ζ η, F k (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ e k * F k ζ η)
    (hGp : ∀ k ζ η, G k (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ e k * G k ζ η)
    (M : ℝ) (hM : 1 ≤ M) (hF : ∀ k ζ η, |F k ζ η| ≤ M) (hG : ∀ k ζ η, |G k ζ η| ≤ M)
    (cost : K → ℝ) (hcost : ∀ k, 0 ≤ cost k) (hdiff : ∀ k ζ η, |F k ζ η - G k ζ η| ≤ cost k)
    (g : P → (J → Bool) → ℝ) (base : P → ℝ) (C shift rough : ℝ)
    (hC : 1 ≤ C) (hshift : 0 ≤ shift) (hrough : 0 ≤ rough) (hr1 : rough ≤ 1) (hsr : shift ≤ rough)
    (hg : ∀ i ζ, |g i ζ| ≤ C) (hb : ∀ i, |base i| ≤ C)
    (hgb : ∀ i ζ, |g i ζ - base i| ≤ C * rough) :
    |independentSigns.expect (fun ζ => shift ^ (∑ k, e k) *
      Walsh.resampleAverage T (fun η => (∏ k, F k ζ η) - ∏ k, G k ζ η) ζ * ∏ i, g i ζ)| ≤
      (M ^ Fintype.card K * ∑ k, cost k) *
        (C ^ Fintype.card P * ((Fintype.card P : ℝ) * C + 1)) * (shift * rough) := by
  let H := fun ζ η => (∏ k, F k ζ η) - ∏ k, G k ζ η
  have hp ζ η : H (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ (∑ k, e k) * H ζ η := by
    simp only [H, hFp, hGp, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_sub]
  have hbound ζ η : |H ζ η| ≤ M ^ Fintype.card K * ∑ k, cost k := by
    have hh := abs_prod_sub_prod_le_bounded Finset.univ (fun k => F k ζ η) (fun k => G k ζ η)
      M hM (fun k _ => hF k ζ η) (fun k _ => hG k ζ η)
    simp only [Finset.card_univ] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hdiff k ζ η))
      (pow_nonneg (zero_le_one.trans hM) _))
  exact parity_weighted_scalar_product_shift_bound (∑ k, e k) he (fun ζ => Walsh.resampleAverage T (H ζ) ζ)
    (Walsh.resampleAverage_simultaneous_parity T H _ hp) g base
    (M ^ Fintype.card K * ∑ k, cost k) C shift rough
    (mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) (Finset.sum_nonneg (fun k _ => hcost k)))
    hC hshift hrough hr1 hsr (fun ζ => FiniteLaw.abs_expect_le_bound _ _ _ (fun fresh =>
      hbound ζ (Walsh.resample T ζ fresh))) hg hb hgb

end CausalLowerbound.PartC

import CausalLowerbound.PartC.ScalarParityBounds
import CausalLowerbound.PartC.ResamplingParity

/-! Shared-sign resampling with general scalar coefficients near a fixed
baseline. The estimate preserves the product of shift and rough amplitudes
for every positive total selected degree. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB
variable {J I K : Type*} [Fintype J] [DecidableEq J] [Fintype I] [Fintype K]

theorem resampled_product_scalar_shift_bound (T : Finset J) (e : K → ℕ) (he : 0 < ∑ k, e k)
    (F : K → (J → Bool) → (J → Bool) → ℝ)
    (hparity : ∀ k ζ η, F k (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ e k * F k ζ η)
    (M : ℝ) (hM : 1 ≤ M) (hF : ∀ k ζ η, |F k ζ η| ≤ M)
    (cost : K → J → ℝ) (hcost0 : ∀ k j, 0 ≤ cost k j)
    (hcost : ∀ k ζ j η η', (∀ i, i ≠ j → η i = η' i) → |F k ζ η - F k ζ η'| ≤ cost k j)
    (g : I → (J → Bool) → ℝ) (base : I → ℝ) (C shift rough : ℝ)
    (hC : 1 ≤ C) (hshift : 0 ≤ shift) (hrough : 0 ≤ rough) (hr1 : rough ≤ 1) (hsr : shift ≤ rough)
    (hg : ∀ i ζ, |g i ζ| ≤ C) (hb : ∀ i, |base i| ≤ C)
    (hgb : ∀ i ζ, |g i ζ - base i| ≤ C * rough) :
    |independentSigns.expect (fun ζ => shift ^ (∑ k, e k) *
      ((∏ k, F k ζ ζ) - Walsh.resampleAverage T (fun η => ∏ k, F k ζ η) ζ) * ∏ i, g i ζ)| ≤
      (M ^ Fintype.card K * ∑ k, ∑ j ∈ T, cost k j) *
        (C ^ Fintype.card I * ((Fintype.card I : ℝ) * C + 1)) * (shift * rough) := by
  let P := fun ζ η => ∏ k, F k ζ η
  have hp ζ η : P (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ (∑ k, e k) * P ζ η := by
    simp only [P, hparity, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have herror ζ : P (Walsh.flip ζ) (Walsh.flip ζ) -
      Walsh.resampleAverage T (P (Walsh.flip ζ)) (Walsh.flip ζ) =
        (-1) ^ (∑ k, e k) * (P ζ ζ - Walsh.resampleAverage T (P ζ) ζ) := by
    rw [hp, Walsh.resampleAverage_simultaneous_parity T P _ hp, mul_sub]
  exact parity_weighted_scalar_product_shift_bound (∑ k, e k) he
    (fun ζ => P ζ ζ - Walsh.resampleAverage T (P ζ) ζ) herror g base
    (M ^ Fintype.card K * ∑ k, ∑ j ∈ T, cost k j) C shift rough
    (mul_nonneg (pow_nonneg (by linarith) _)
      (Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun j _ => hcost0 k j))))
    hC hshift hrough hr1 hsr
    (fun ζ => Walsh.resampleAverage_product_sub_bound T (fun k => F k ζ) M hM
      (fun k η => hF k ζ η) cost (fun k j η η' h => hcost k ζ j η η' h) ζ) hg hb hgb

end CausalLowerbound.PartC

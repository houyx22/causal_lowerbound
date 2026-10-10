import CausalLowerbound.HolderScaling
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Deterministic two-scale cancellation.  Geometry supplies the Taylor
remainders and the small auxiliary weights; these lemmas combine them with
the exact exponents, including smoothness at and below one. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.UpperBound

def twoScaleModulus (a ℓ r : ℝ) : ℝ := ℓ ^ min a 1 * r ^ max (a - 1) 0

theorem twoScaleModulus_nonneg (a ℓ r : ℝ) (hℓ : 0 ≤ ℓ) (hr : 0 ≤ r) :
    0 ≤ twoScaleModulus a ℓ r := by
  exact mul_nonneg (Real.rpow_nonneg hℓ _) (Real.rpow_nonneg hr _)

theorem close_remainder_le_twoScaleModulus (a ℓ r : ℝ)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) : ℓ ^ a ≤ twoScaleModulus a ℓ r := by
  have hr : 0 < r := hℓ.trans_le hℓr
  by_cases ha : a ≤ 1
  · simp [twoScaleModulus, min_eq_left ha, max_eq_right (by linarith : a - 1 ≤ 0)]
  · have ha' : 1 ≤ a := le_of_lt (lt_of_not_ge ha)
    rw [twoScaleModulus, min_eq_right ha', max_eq_left (by linarith : 0 ≤ a - 1),
      Real.rpow_one]
    have hp := Real.rpow_le_rpow hℓ.le hℓr (show 0 ≤ a - 1 by linarith)
    have he : ℓ ^ a = ℓ * ℓ ^ (a - 1) := by
      rw [Real.rpow_sub_one hℓ.ne']
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hp hℓ.le

theorem auxiliary_remainder_le_twoScaleModulus (a ℓ r : ℝ)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) : (ℓ / r) * r ^ a ≤ twoScaleModulus a ℓ r := by
  have hr : 0 < r := hℓ.trans_le hℓr
  have he : (ℓ / r) * r ^ a = ℓ * r ^ (a - 1) := by
    rw [Real.rpow_sub_one hr.ne']
    ring
  rw [he]
  by_cases ha : a ≤ 1
  · rw [twoScaleModulus, min_eq_left ha, max_eq_right (by linarith : a - 1 ≤ 0),
      Real.rpow_zero, mul_one]
    have hp := Real.rpow_le_rpow_of_nonpos hℓ hℓr (show a - 1 ≤ 0 by linarith)
    calc
      ℓ * r ^ (a - 1) ≤ ℓ * ℓ ^ (a - 1) := mul_le_mul_of_nonneg_left hp hℓ.le
      _ = ℓ ^ a := by rw [Real.rpow_sub_one hℓ.ne']; field_simp
  · have ha' : 1 ≤ a := le_of_lt (lt_of_not_ge ha)
    simp [twoScaleModulus, min_eq_right ha', max_eq_left (by linarith : 0 ≤ a - 1)]

/-- The product of the two nuisance moduli is exactly the bias term in the
master bound; no asymptotic comparison is needed at this step. -/
theorem twoScaleModulus_product (α β ℓ r : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) :
    twoScaleModulus α ℓ r * twoScaleModulus β ℓ r =
      ℓ ^ (min α 1 + min β 1) * r ^ (α + β - (min α 1 + min β 1)) := by
  have he (a : ℝ) : max (a - 1) 0 = a - min a 1 := by
    by_cases ha : a ≤ 1
    · rw [min_eq_left ha, max_eq_right (by linarith : a - 1 ≤ 0)]
      ring
    · rw [min_eq_right (le_of_not_ge ha), max_eq_left (by linarith : 0 ≤ a - 1)]
  unfold twoScaleModulus
  rw [Real.rpow_add hℓ, show α + β - (min α 1 + min β 1) =
    max (α - 1) 0 + max (β - 1) 0 by rw [he, he]; ring, Real.rpow_add hr]
  ring

theorem contrast_le_remainders {A : Type*} [Fintype A]
    (w₀ w₁ g₀ g₁ p₀ p₁ : ℝ) (w g p : A → ℝ) (W R₁ R : ℝ)
    (hW : 0 ≤ W)
    (hcancel : w₀ * p₀ + w₁ * p₁ + ∑ i, w i * p i = 0)
    (hanchor : g₀ = p₀) (hclose : |w₁| ≤ 1) (haux : ∀ i, |w i| ≤ W)
    (hcloseR : |g₁ - p₁| ≤ R₁) (hauxR : ∀ i, |g i - p i| ≤ R) :
    |w₀ * g₀ + w₁ * g₁ + ∑ i, w i * g i| ≤ R₁ + Fintype.card A * W * R := by
  have he : w₀ * g₀ + w₁ * g₁ + ∑ i, w i * g i =
      w₁ * (g₁ - p₁) + ∑ i, w i * (g i - p i) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [hanchor]
    linarith
  rw [he]
  have hh : |w₁ * (g₁ - p₁)| ≤ R₁ := by
    rw [abs_mul]
    exact (mul_le_mul hclose hcloseR (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have ht : |∑ i, w i * (g i - p i)| ≤ Fintype.card A * W * R := by
    calc
      _ ≤ ∑ i, |w i * (g i - p i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : A, W * R := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul (haux i) (hauxR i) (abs_nonneg _) hW
      _ = _ := by simp [mul_assoc]
  exact (abs_add_le _ _).trans (add_le_add hh ht)

theorem contrast_le_twoScaleModulus {A : Type*} [Fintype A]
    (w₀ w₁ g₀ g₁ p₀ p₁ : ℝ) (w g p : A → ℝ) (C W a ℓ r : ℝ)
    (hC : 0 ≤ C) (hW : 0 ≤ W) (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r)
    (hcancel : w₀ * p₀ + w₁ * p₁ + ∑ i, w i * p i = 0)
    (hanchor : g₀ = p₀) (hclose : |w₁| ≤ 1) (haux : ∀ i, |w i| ≤ W * (ℓ / r))
    (hcloseR : |g₁ - p₁| ≤ C * ℓ ^ a) (hauxR : ∀ i, |g i - p i| ≤ C * r ^ a) :
    |w₀ * g₀ + w₁ * g₁ + ∑ i, w i * g i| ≤
      C * (1 + Fintype.card A * W) * twoScaleModulus a ℓ r := by
  have hr : 0 < r := hℓ.trans_le hℓr
  have hb := contrast_le_remainders w₀ w₁ g₀ g₁ p₀ p₁ w g p
    (W * (ℓ / r)) (C * ℓ ^ a) (C * r ^ a) (by positivity)
    hcancel hanchor hclose haux hcloseR hauxR
  have h₁ := mul_le_mul_of_nonneg_left (close_remainder_le_twoScaleModulus a ℓ r hℓ hℓr) hC
  have h₂ := mul_le_mul_of_nonneg_left
    (auxiliary_remainder_le_twoScaleModulus a ℓ r hℓ hℓr)
    (show 0 ≤ C * Fintype.card A * W by positivity)
  nlinarith

end CausalLowerbound.UpperBound

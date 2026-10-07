import CausalLowerbound.PartC.MixedLikelihoodPolynomials
import CausalLowerbound.FiniteProductBounds

/-! The target-side likelihood difference retains its physical amplitude.
These bounds apply pointwise to the actual polynomial cells, including
configurations where the spatial matching hypotheses do not hold. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry MvPolynomial
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I]

theorem RoughPropensity.realField_abs_le (R T ja δ X : ℝ)
    (hR : |R| ≤ 1) (hT : |T| ≤ 1) (hX : |ja * X| ≤ 1) :
    |RoughPropensity.realField R T ja δ X| ≤ 2 * |δ| := by
  have he : RoughPropensity.realField R T ja δ X = δ * T * (ja * X + R) := by
    unfold RoughPropensity.realField
    ring
  rw [he, abs_mul, abs_mul]
  have hs : |ja * X + R| ≤ 2 := (abs_add _ _).trans (by linarith)
  calc
    _ ≤ (|δ| * 1) * 2 := mul_le_mul
      (mul_le_mul_of_nonneg_left hT (abs_nonneg δ)) hs (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem RoughPropensity.likelihood_abs_le (R T ja smooth X : ℝ)
    (hR : |R| ≤ 1) (hT : |T| ≤ 1) (hX : |ja * X| ≤ 1) (hs : |smooth| ≤ 1) :
    |RoughPropensity.likelihood R T ja smooth X| ≤ 4 := by
  have hp : |R * ja * X| ≤ 1 := by
    rw [mul_assoc, abs_mul]
    exact (mul_le_mul hR hX (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hq : |T * smooth| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hT hs (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hp' : |1 + R * ja * X| ≤ 2 := (abs_add _ _).trans (by rw [abs_one]; linarith)
  have hq' : |1 + T * smooth| ≤ 2 := (abs_add _ _).trans (by rw [abs_one]; linarith)
  rw [RoughPropensity.likelihood, abs_mul]
  exact (mul_le_mul hp' hq' (abs_nonneg _) (by norm_num)).trans (by norm_num)

theorem mixedPropensityCellPolynomial_sub_abs_le
    (Q : ℕ) (S : Finset (d → ℤ)) (U : S × CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : d → ℝ) (y : Bool × Bool)
    (hrough : |ja * physicalRoughField x₀ ℓ h ζ x| ≤ 1) :
    |eval U (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ x y) -
      eval U (mixedPropensityCellPolynomial Q false S x₀ ℓ r h ja b t ζ x y)| ≤
      |ja * b * t| / 2 := by
  have he : eval U (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ x y) -
      eval U (mixedPropensityCellPolynomial Q false S x₀ ℓ r h ja b t ζ x y) =
      (1 / 4) * RoughPropensity.realField (sign y.1) (sign y.2) ja
        (targetField x₀ h (ja * b * t) x) (physicalRoughField x₀ ℓ h ζ x) := by
    simp only [mixedPropensityCellPolynomial, map_mul, eval_C, propensitySitePolynomial_eval,
      Bool.false_eq_true, if_false, if_true]
    ring
  rw [he, abs_mul]
  have hb := RoughPropensity.realField_abs_le (sign y.1) (sign y.2) ja
    (targetField x₀ h (ja * b * t) x) (physicalRoughField x₀ ℓ h ζ x)
    (abs_sign _).le (abs_sign _).le hrough
  have ht := targetField_abs_le x₀ h (ja * b * t) x
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  linarith

theorem mixedPropensityCellPolynomial_abs_le_two
    (Q : ℕ) (side : Bool) (S : Finset (d → ℤ)) (U : S × CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : d → ℝ) (y : Bool × Bool)
    (hrough : |ja * physicalRoughField x₀ ℓ h ζ x| ≤ 1)
    (hsmooth : |b * eval U (globalCarriedPolynomial Q S x₀ r x)| ≤ 1)
    (htarget : |ja * b * t| ≤ 1) :
    |eval U (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ x y)| ≤ 2 := by
  have hbase : |eval U (mixedPropensityCellPolynomial Q false S x₀ ℓ r h ja b t ζ x y)| ≤ 1 := by
    simp only [mixedPropensityCellPolynomial, map_mul, eval_C, propensitySitePolynomial_eval,
      Bool.false_eq_true, if_false, add_zero, abs_mul]
    have hb := RoughPropensity.likelihood_abs_le (sign y.1) (sign y.2) ja
      (b * eval U (globalCarriedPolynomial Q S x₀ r x)) (physicalRoughField x₀ ℓ h ζ x)
      (abs_sign _).le (abs_sign _).le hrough hsmooth
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    linarith
  cases side with
  | false => exact hbase.trans (by norm_num)
  | true =>
    have hd := mixedPropensityCellPolynomial_sub_abs_le Q S U x₀ ℓ r h ja b t ζ x y hrough
    have he := abs_add
      (eval U (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ x y) -
        eval U (mixedPropensityCellPolynomial Q false S x₀ ℓ r h ja b t ζ x y))
      (eval U (mixedPropensityCellPolynomial Q false S x₀ ℓ r h ja b t ζ x y))
    rw [sub_add_cancel] at he
    linarith

theorem mixedPropensityCellProduct_sub_abs_le
    (Q : ℕ) (S : Finset (d → ℤ)) (U : S × CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hrough : ∀ i, |ja * physicalRoughField x₀ ℓ h ζ (x i)| ≤ 1)
    (hsmooth : ∀ i, |b * eval U (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1)
    (htarget : |ja * b * t| ≤ 1) :
    |(∏ i, eval U (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ (x i) (y i))) -
      ∏ i, eval U (mixedPropensityCellPolynomial Q false S x₀ ℓ r h ja b t ζ (x i) (y i))| ≤
      (2 : ℝ) ^ Fintype.card I * Fintype.card I * (|ja * b * t| / 2) := by
  have hb := abs_prod_sub_prod_le_bounded Finset.univ
    (fun i => eval U (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ (x i) (y i)))
    (fun i => eval U (mixedPropensityCellPolynomial Q false S x₀ ℓ r h ja b t ζ (x i) (y i)))
    2 (by norm_num)
    (fun i _ => mixedPropensityCellPolynomial_abs_le_two Q true S U x₀ ℓ r h ja b t ζ (x i) (y i)
      (hrough i) (hsmooth i) htarget)
    (fun i _ => mixedPropensityCellPolynomial_abs_le_two Q false S U x₀ ℓ r h ja b t ζ (x i) (y i)
      (hrough i) (hsmooth i) htarget)
  simp only [Finset.card_univ] at hb
  apply hb.trans
  calc
    _ ≤ (2 : ℝ) ^ Fintype.card I * ∑ _i : I, (|ja * b * t| / 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
        mixedPropensityCellPolynomial_sub_abs_le Q S U x₀ ℓ r h ja b t ζ (x i) (y i) (hrough i)))
        (by positivity)
    _ = _ := by simp [mul_assoc]

end CausalLowerbound.PartC

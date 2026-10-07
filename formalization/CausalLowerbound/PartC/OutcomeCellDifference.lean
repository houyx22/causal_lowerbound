import CausalLowerbound.PartC.MixedLikelihoodPolynomials
import CausalLowerbound.PartC.OutcomeTaylorBounds
import CausalLowerbound.FiniteProductBounds

/-! The actual rough-outcome likelihood increment has the target
amplitude a*t*jb. These pointwise bounds also apply on configurations
without separation or assignment-interior hypotheses. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry MvPolynomial
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I]

theorem RoughOutcome.realField_abs_le (R T smooth δ : ℝ)
    (hR : |R| ≤ 1) (hT : |T| ≤ 1) (hs : |smooth| ≤ 1) :
    |RoughOutcome.realField R T smooth δ| ≤ 6 * |δ| := by
  have hs2 : |smooth| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hs
  have hp : |1 - 3 * smooth ^ 2| ≤ 4 := by
    apply (abs_sub _ _).trans
    rw [abs_one, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  have hn : |(-2 : ℝ) * smooth| ≤ 2 := by
    rw [abs_mul]
    norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hrp : |R * (1 - 3 * smooth ^ 2)| ≤ 4 := by
    rw [abs_mul]
    exact (mul_le_mul hR hp (abs_nonneg _) zero_le_one).trans_eq (one_mul 4)
  have hsum : |-2 * smooth + R * (1 - 3 * smooth ^ 2)| ≤ 6 :=
    (abs_add _ _).trans (by linarith)
  have he : RoughOutcome.realField R T smooth δ = δ * T * (-2 * smooth + R * (1 - 3 * smooth ^ 2)) := by
    unfold RoughOutcome.realField
    ring
  rw [he, abs_mul, abs_mul]
  calc
    _ ≤ (|δ| * 1) * 6 := mul_le_mul
      (mul_le_mul_of_nonneg_left hT (abs_nonneg δ)) hsum (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem mixedOutcomeCellPolynomial_sub_abs_le
    (Q : ℕ) (S : Finset (d → ℤ)) (U : S × CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : d → ℝ) (y : Bool × Bool)
    (hsmooth : |a * eval U (globalCarriedPolynomial Q S x₀ r x)| ≤ 1) :
    |eval U (mixedOutcomeCellPolynomial Q true S x₀ ℓ r h a jb t ζ x y) -
      eval U (mixedOutcomeCellPolynomial Q false S x₀ ℓ r h a jb t ζ x y)| ≤
      (3 / 2 : ℝ) * |a * t * jb| := by
  have he : eval U (mixedOutcomeCellPolynomial Q true S x₀ ℓ r h a jb t ζ x y) -
      eval U (mixedOutcomeCellPolynomial Q false S x₀ ℓ r h a jb t ζ x y) =
      (1 / 4) * RoughOutcome.realField (sign y.1) (sign y.2)
        (a * eval U (globalCarriedPolynomial Q S x₀ r x)) (targetField x₀ h (a * t * jb) x) := by
    simp only [mixedOutcomeCellPolynomial, map_mul, eval_C, outcomeSitePolynomial_eval,
      Bool.false_eq_true, if_false, if_true]
    ring
  rw [he, abs_mul]
  have hb := RoughOutcome.realField_abs_le (sign y.1) (sign y.2)
    (a * eval U (globalCarriedPolynomial Q S x₀ r x)) (targetField x₀ h (a * t * jb) x)
    (abs_sign _).le (abs_sign _).le hsmooth
  have ht := targetField_abs_le x₀ h (a * t * jb) x
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  linarith

theorem mixedOutcomeCellPolynomial_abs_le_five
    (Q : ℕ) (side : Bool) (S : Finset (d → ℤ)) (U : S × CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : d → ℝ) (y : Bool × Bool)
    (hrough : |jb * physicalRoughField x₀ ℓ h ζ x| ≤ 1)
    (hη : |physicalRoughCorrection x₀ ℓ h (a * t) x| ≤ 3)
    (hsmooth : |a * eval U (globalCarriedPolynomial Q S x₀ r x)| ≤ 1)
    (htarget : |a * t * jb| ≤ 1) :
    |eval U (mixedOutcomeCellPolynomial Q side S x₀ ℓ r h a jb t ζ x y)| ≤ 5 := by
  have hbase : |eval U (mixedOutcomeCellPolynomial Q false S x₀ ℓ r h a jb t ζ x y)| ≤ 3 := by
    simp only [mixedOutcomeCellPolynomial, map_mul, eval_C, outcomeSitePolynomial_eval,
      Bool.false_eq_true, if_false, add_zero, abs_mul]
    have hb := (outcomeTaylorCoefficient_unit_bounds (sign y.1) (sign y.2) jb
      (physicalRoughCorrection x₀ ℓ h (a * t) x) (a * eval U (globalCarriedPolynomial Q S x₀ r x))
      (physicalRoughField x₀ ℓ h ζ x) 1 (abs_sign _).le (abs_sign _).le hη hsmooth
      (by norm_num) (by norm_num) hrough 0).1
    simp only [outcomeTaylorCoefficient, if_pos rfl, if_true] at hb
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    linarith
  cases side with
  | false => exact hbase.trans (by norm_num)
  | true =>
    have hd := mixedOutcomeCellPolynomial_sub_abs_le Q S U x₀ ℓ r h a jb t ζ x y hsmooth
    have he := abs_add
      (eval U (mixedOutcomeCellPolynomial Q true S x₀ ℓ r h a jb t ζ x y) -
        eval U (mixedOutcomeCellPolynomial Q false S x₀ ℓ r h a jb t ζ x y))
      (eval U (mixedOutcomeCellPolynomial Q false S x₀ ℓ r h a jb t ζ x y))
    rw [sub_add_cancel] at he
    linarith

theorem mixedOutcomeCellProduct_sub_abs_le
    (Q : ℕ) (S : Finset (d → ℤ)) (U : S × CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hrough : ∀ i, |jb * physicalRoughField x₀ ℓ h ζ (x i)| ≤ 1)
    (hη : ∀ i, |physicalRoughCorrection x₀ ℓ h (a * t) (x i)| ≤ 3)
    (hsmooth : ∀ i, |a * eval U (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1)
    (htarget : |a * t * jb| ≤ 1) :
    |(∏ i, eval U (mixedOutcomeCellPolynomial Q true S x₀ ℓ r h a jb t ζ (x i) (y i))) -
      ∏ i, eval U (mixedOutcomeCellPolynomial Q false S x₀ ℓ r h a jb t ζ (x i) (y i))| ≤
      (5 : ℝ) ^ Fintype.card I * Fintype.card I * ((3 / 2 : ℝ) * |a * t * jb|) := by
  have hb := abs_prod_sub_prod_le_bounded Finset.univ
    (fun i => eval U (mixedOutcomeCellPolynomial Q true S x₀ ℓ r h a jb t ζ (x i) (y i)))
    (fun i => eval U (mixedOutcomeCellPolynomial Q false S x₀ ℓ r h a jb t ζ (x i) (y i)))
    5 (by norm_num)
    (fun i _ => mixedOutcomeCellPolynomial_abs_le_five Q true S U x₀ ℓ r h a jb t ζ (x i) (y i)
      (hrough i) (hη i) (hsmooth i) htarget)
    (fun i _ => mixedOutcomeCellPolynomial_abs_le_five Q false S U x₀ ℓ r h a jb t ζ (x i) (y i)
      (hrough i) (hη i) (hsmooth i) htarget)
  simp only [Finset.card_univ] at hb
  apply hb.trans
  calc
    _ ≤ (5 : ℝ) ^ Fintype.card I * ∑ _i : I, ((3 / 2 : ℝ) * |a * t * jb|) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
        mixedOutcomeCellPolynomial_sub_abs_le Q S U x₀ ℓ r h a jb t ζ (x i) (y i) (hsmooth i)))
        (by positivity)
    _ = _ := by simp [mul_assoc]

end CausalLowerbound.PartC

import CausalLowerbound.PartC.PropensityChoiceBounds

/-! Keep the full smooth-amplitude power in each observation choice.
The effective parity shift is b*t; retaining this factor avoids the
unnecessary and scale-incompatible condition t ≤ ja. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry MvPolynomial
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def propensityChoiceNormalizedCoefficient (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (r b : ℝ) (x : I → d → ℝ) (y : I → Bool × Bool)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) (s : I → Option S) : ℝ :=
  choiceBase (fun i => (1 / 4) * (1 + sign (y i).2 * b *
    eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))) s *
      ∏ i : ShiftPositions s, (1 / 4) * sign (y i.val).2 *
        linearPartition (localCoordinate x₀ r (choiceSite s i).val (x i.val))

theorem propensityChoiceSmoothCoefficient_factor (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (r b : ℝ) (x : I → d → ℝ) (y : I → Bool × Bool)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) (s : I → Option S) :
    propensityChoiceSmoothCoefficient Q ρ S x₀ r b x y ξ s =
      propensityChoiceNormalizedCoefficient Q ρ S x₀ r b x y ξ s * b ^ choiceDegree s := by
  have he (i : ShiftPositions s) : (1 / 4) * sign (y i.val).2 * b *
      linearPartition (localCoordinate x₀ r (choiceSite s i).val (x i.val)) =
      b * ((1 / 4) * sign (y i.val).2 * linearPartition (localCoordinate x₀ r (choiceSite s i).val (x i.val))) := by ring
  unfold propensityChoiceSmoothCoefficient propensityChoiceNormalizedCoefficient
  simp_rw [he]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, choiceDegree]
  ring

theorem propensityObservationCoefficient_false_normalized
    (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h ja b t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) (s : I → Option S) :
    propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s =
      propensityChoiceNormalizedCoefficient Q ρ S x₀ r b x y ξ s * (b * t) ^ choiceDegree s *
        ∏ i, (1 + sign (y i).1 * ja * physicalRoughField x₀ ℓ h ζ (x i)) := by
  rw [propensityObservationCoefficient_false, propensityChoiceSmoothCoefficient_factor, mul_pow]
  ring

theorem propensityChoiceNormalizedCoefficient_abs_le
    (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r b : ℝ)
    (x : I → d → ℝ) (y : I → Bool × Bool) (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q))
    (hsmooth : ∀ i, |b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) (s : I → Option S) :
    |propensityChoiceNormalizedCoefficient Q ρ S x₀ r b x y ξ s| ≤ 1 := by
  have ha (i : I) : |(1 / 4 : ℝ) * (1 + sign (y i).2 * b *
      eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))| ≤ 1 := by
    have hh : |sign (y i).2 * b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1 := by
      rw [mul_assoc, abs_mul, abs_sign, one_mul]
      exact hsmooth i
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have hb := abs_add (1 : ℝ) (sign (y i).2 * b *
      eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
    rw [abs_one] at hb
    linarith
  have hd (i : ShiftPositions s) : |(1 / 4 : ℝ) * sign (y i.val).2 *
      linearPartition (localCoordinate x₀ r (choiceSite s i).val (x i.val))| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_sign, abs_of_nonneg (linearPartition_bounds _).1]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), mul_one]
    linarith [(linearPartition_bounds (localCoordinate x₀ r (choiceSite s i).val (x i.val))).2]
  unfold propensityChoiceNormalizedCoefficient
  rw [abs_mul]
  calc
    _ ≤ (1 : ℝ) * 1 := mul_le_mul (by
      rw [choiceBase, Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => ha i.val)) (by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => hd i)) (abs_nonneg _) zero_le_one
    _ = 1 := by norm_num

theorem propensityChoiceNormalizedCoefficient_sum_bound
    (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r b : ℝ) (hb : 0 ≤ b)
    (x : I → d → ℝ) (y : I → Bool × Bool) (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q))
    (hsmooth : ∀ i, |b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    (∑ s : I → Option S, if 0 < choiceDegree s then
      b * |propensityChoiceNormalizedCoefficient Q ρ S x₀ r b x y ξ s| else 0) ≤
        ((Fintype.card S : ℝ) + 1) ^ Fintype.card I * b := by
  calc
    _ ≤ ∑ _s : I → Option S, b := Finset.sum_le_sum (fun s _ => by
      by_cases hs : 0 < choiceDegree s
      · rw [if_pos hs]
        exact mul_le_of_le_one_right hb (propensityChoiceNormalizedCoefficient_abs_le Q ρ S x₀ r b x y ξ hsmooth s)
      · rw [if_neg hs]
        exact hb)
    _ = _ := by simp [Fintype.card_fun, Fintype.card_option, Nat.cast_add, Nat.cast_pow]

theorem amplitude_shift_factor (a b C t J : ℝ) :
    (b * |a|) * (C * (t * J)) = |a| * (C * ((b * t) * J)) := by ring

theorem mixed_propensity_effective_shift_le (a₀ b₀ r t α β : ℝ)
    (hb₀ : 0 ≤ b₀) (hba : b₀ ≤ a₀) (hr : 0 < r) (hr1 : r ≤ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) (hα1 : α ≤ 1) (hαβ : α ≤ β) :
    (b₀ * r ^ β) * t ≤ a₀ * (t * r) ^ α := by
  have hrr := Real.rpow_le_rpow_of_exponent_ge hr hr1 hαβ
  have htt : t ≤ t ^ α := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1 hα1
  calc
    _ ≤ (a₀ * r ^ α) * t := mul_le_mul_of_nonneg_right
      (mul_le_mul hba hrr (Real.rpow_nonneg hr.le _) (hb₀.trans hba)) ht.le
    _ ≤ (a₀ * r ^ α) * t ^ α := mul_le_mul_of_nonneg_left htt
      (mul_nonneg (hb₀.trans hba) (Real.rpow_nonneg hr.le _))
    _ = _ := by rw [Real.mul_rpow ht.le hr.le]; ring

end CausalLowerbound.PartC

import CausalLowerbound.PartC.PropensityObservationWeights
import CausalLowerbound.FiniteBounds

/-! Every nonempty observation choice contributes at least one factor b.
Summing the actual smooth coefficients therefore retains b; the number
of choices depends only on the observations and their incident blocks. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry MvPolynomial
variable {I K d : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  [Fintype d] [DecidableEq d]

theorem nonempty_choice_coefficient_abs_le
    (a : I → ℝ) (δ : I → K → ℝ) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ha : ∀ i, |a i| ≤ 1) (hδ : ∀ i k, |δ i k| ≤ b)
    (s : I → Option K) (hs : 0 < choiceDegree s) :
    |choiceBase a s * ∏ i : ShiftPositions s, δ i.val (choiceSite s i)| ≤ b := by
  have hbase : |choiceBase a s| ≤ 1 := by
    rw [choiceBase, Finset.abs_prod]
    exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => ha i.val)
  have hshift : |∏ i : ShiftPositions s, δ i.val (choiceSite s i)| ≤ b ^ choiceDegree s := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i : ShiftPositions s, b := Finset.prod_le_prod
        (fun i _ => abs_nonneg _) (fun i _ => hδ i.val (choiceSite s i))
      _ = _ := by simp [choiceDegree]
  have hp : b ^ choiceDegree s ≤ b := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
    rw [hn, pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hb hb1) hb).trans (by simp)
  rw [abs_mul]
  exact (mul_le_mul hbase (hshift.trans hp) (abs_nonneg _) zero_le_one).trans (by simp)

theorem propensityChoiceSmoothCoefficient_abs_le
    (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r b : ℝ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (x : I → d → ℝ) (y : I → Bool × Bool)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q))
    (hsmooth : ∀ i, |b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1)
    (s : I → Option S) (hs : 0 < choiceDegree s) :
    |propensityChoiceSmoothCoefficient Q ρ S x₀ r b x y ξ s| ≤ b := by
  unfold propensityChoiceSmoothCoefficient
  refine nonempty_choice_coefficient_abs_le
    (fun i : I => (1 / 4) * (1 + sign (y i).2 * b *
      eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2) (globalCarriedPolynomial Q S x₀ r (x i))))
    (fun (i : I) (k : S) => (1 / 4) * sign (y i).2 * b * linearPartition (localCoordinate x₀ r k.val (x i)))
    b hb hb1 ?_ ?_ s hs
  · intro i
    have hsign : |sign (y i).2 * b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1 := by
      rw [mul_assoc, abs_mul, abs_sign, one_mul]
      exact hsmooth i
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have hh := abs_add (1 : ℝ) (sign (y i).2 * b *
      eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
    rw [abs_one] at hh
    linarith
  · intro i k
    rw [abs_mul, abs_mul, abs_mul, abs_sign, abs_of_nonneg hb,
      abs_of_nonneg (linearPartition_bounds _).1,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    nlinarith [(linearPartition_bounds (localCoordinate x₀ r k.val (x i))).2]

theorem propensityChoiceSmoothCoefficient_sum_bound
    (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r b : ℝ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (x : I → d → ℝ) (y : I → Bool × Bool)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q))
    (hsmooth : ∀ i, |b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    (∑ s : I → Option S, if 0 < choiceDegree s then
      |propensityChoiceSmoothCoefficient Q ρ S x₀ r b x y ξ s| else 0) ≤
        ((Fintype.card S : ℝ) + 1) ^ Fintype.card I * b := by
  calc
    _ ≤ ∑ _s : I → Option S, b := Finset.sum_le_sum (fun s _ => by
      by_cases hs : 0 < choiceDegree s
      · rw [if_pos hs]
        exact propensityChoiceSmoothCoefficient_abs_le Q ρ S x₀ r b hb hb1 x y ξ hsmooth s hs
      · rw [if_neg hs]
        exact hb)
    _ = _ := by simp [Fintype.card_fun, Fintype.card_option, Nat.cast_add, Nat.cast_pow]

end CausalLowerbound.PartC

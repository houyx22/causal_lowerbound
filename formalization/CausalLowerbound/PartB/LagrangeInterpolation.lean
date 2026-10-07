import CausalLowerbound.PartB.PaperWiener
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Exact interpolation in the paper's coefficient space. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry
open MvPolynomial

variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [LinearOrder V]

theorem pairLinear_eval (u v : d → ℝ) (x : d × Bool → ℝ) :
    eval x (pairLinear u v) =
      (∑ a, (x a - embedding v a) * (embedding u a - embedding v a)) / pairDenominator u v := by
  rw [pairLinear, map_sum, Fintype.sum_option]
  simp only [atomDegree, atomSign, Option.elim_none, Option.elim_some,
    eval_monomial, Finsupp.prod_zero_index, mul_one, Finsupp.prod_single_index,
    pow_one, pow_zero, neg_one_mul, one_mul, elementaryCoefficient]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  have hn : (∑ a, (x a - embedding v a) * (embedding u a - embedding v a)) =
      (∑ a, (embedding u a - embedding v a) * x a) -
        ∑ a, embedding v a * (embedding u a - embedding v a) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hn]
  ring

theorem pairLinear_eval_right (u v : d → ℝ) : eval (embedding v) (pairLinear u v) = 0 := by
  rw [pairLinear_eval]
  simp

theorem pairLinear_eval_left (u v : d → ℝ) (h : chordDistance u v ≠ 0) :
    eval (embedding u) (pairLinear u v) = 1 := by
  rw [pairLinear_eval]
  simpa only [pairDenominator, pow_two] using div_self (pairDenominator_ne_zero u v h)

theorem completeLagrangePolynomial_interpolates (u : V × d → ℝ)
    (hu : ∀ i j, i ≠ j → chordDistance (configurationSite u i) (configurationSite u j) ≠ 0)
    (i j : V) :
    eval (embedding (configurationSite u j)) (completeLagrangePolynomial i u) =
      if i = j then 1 else 0 := by
  rw [completeLagrangePolynomial, map_prod]
  by_cases h : i = j
  · subst j
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro k _
    exact pairLinear_eval_left _ _ (hu i k.val k.property.symm)
  · rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨j, Ne.symm h⟩ : {j : V // j ≠ i}))
      (pairLinear_eval_right _ _)

theorem pairLinear_degree (u v : d → ℝ) : (pairLinear u v).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro k _
  refine (totalDegree_monomial_le _ _).trans ?_
  cases k <;> simp [atomDegree]

theorem completeLagrangePolynomial_degree (i : V) (u : V × d → ℝ) :
    (completeLagrangePolynomial i u).totalDegree ≤ Fintype.card V - 1 := by
  refine (totalDegree_finset_prod _ _).trans ?_
  calc
    _ ≤ ∑ _j : {j : V // j ≠ i}, (1 : ℕ) :=
      Finset.sum_le_sum (fun _ _ => pairLinear_degree _ _)
    _ = _ := by simp [Fintype.card_subtype_compl]

/-- A polynomial of the prescribed total degree expands in exactly the
canonical coefficient basis used by the completed Wiener estimate. -/
theorem polynomial_canonical_expansion (Q : ℕ) (hQ : 0 < Q)
    (P : MvPolynomial (d × Bool) ℝ) (hP : P.totalDegree ≤ Q - 1) :
    P = ∑ b : CoefficientExponent d Q, monomial (polynomialBasisDegree b)
      (coeff (polynomialBasisDegree b) P) := by
  classical
  apply MvPolynomial.ext
  intro κ
  simp only [coeff_sum, coeff_monomial]
  by_cases hκ : (∑ a, κ a) ≤ Q - 1
  · obtain ⟨b, hb⟩ := polynomialBasisDegree_complete Q hQ κ hκ
    rw [Finset.sum_eq_single b]
    · simp [hb]
    · intro b' _ hbb
      rw [if_neg]
      intro he
      exact hbb (polynomialBasisDegree_injective Q (he.trans hb.symm))
    · simp
  · have hz : coeff κ P = 0 := by
      apply coeff_eq_zero_of_totalDegree_lt
      have ht : P.totalDegree < ∑ a, κ a := lt_of_le_of_lt hP (lt_of_not_ge hκ)
      change P.totalDegree < κ.sum (fun _ n => n)
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact ht
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro he
    apply hκ
    rw [← he]
    exact b.property

def polynomialFeature {Q : ℕ} (u : d → ℝ) (b : CoefficientExponent d Q) : ℝ :=
  ∏ a, embedding u a ^ (b.val a).val

theorem canonical_expansion_eval (Q : ℕ) (hQ : 0 < Q)
    (P : MvPolynomial (d × Bool) ℝ) (hP : P.totalDegree ≤ Q - 1) (u : d → ℝ) :
    eval (embedding u) P =
      ∑ b : CoefficientExponent d Q, coeff (polynomialBasisDegree b) P * polynomialFeature u b := by
  conv_lhs => rw [polynomial_canonical_expansion Q hQ P hP]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [eval_monomial, Finsupp.prod_fintype]
  · rfl
  · intro a
    simp

/-- The coefficients already used to define J are actual Lagrange vectors. -/
theorem lagrangeCoefficient_interpolates (Q : ℕ) (hQ : 0 < Q)
    (hcard : Fintype.card V ≤ Q) (u : V × d → ℝ)
    (hu : ∀ i j, i ≠ j → chordDistance (configurationSite u i) (configurationSite u j) ≠ 0)
    (i j : V) :
    (∑ b : CoefficientExponent d Q,
      lagrangeCoefficient edgeLeft edgeRight i (polynomialBasisDegree b) u *
        polynomialFeature (configurationSite u j) b) = if i = j then 1 else 0 := by
  simp only [lagrangeCoefficient, lagrangePolynomial_complete]
  rw [← canonical_expansion_eval Q hQ _
    ((completeLagrangePolynomial_degree i u).trans (Nat.sub_le_sub_right hcard 1))]
  exact completeLagrangePolynomial_interpolates u hu i j

end CausalLowerbound.PartB.ShellGeometry

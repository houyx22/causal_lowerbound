import CausalLowerbound.PartB.PolynomialMoments

/-! Split each monomial in a polynomial of all block coefficients into
one monomial per block. The degree needed in each block is bounded by the
total degree of the original polynomial, including its constant term. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry MvPolynomial
variable {K A : Type*} [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]

def blockExponent (m : (K × A) →₀ ℕ) (k : K) : A →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun a => m (k, a))

omit [Fintype K] [DecidableEq K] [DecidableEq A] in
@[simp] theorem blockExponent_apply (m : (K × A) →₀ ℕ) (k : K) (a : A) :
    blockExponent m k a = m (k, a) := by
  simp [blockExponent]

def blockMonomial (m : (K × A) →₀ ℕ) (k : K) : MvPolynomial A ℝ :=
  monomial (blockExponent m k) 1

theorem blockMonomial_eval (m : (K × A) →₀ ℕ) (k : K) (U : A → ℝ) :
    eval U (blockMonomial m k) = ∏ a, U a ^ m (k, a) := by
  simp only [blockMonomial, eval_monomial, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [blockExponent_apply]

theorem eval_block_expansion (p : MvPolynomial (K × A) ℝ) (U : K → A → ℝ) :
    eval (fun ka => U ka.1 ka.2) p =
      ∑ m ∈ p.support, p.coeff m * ∏ k, eval (U k) (blockMonomial m k) := by
  simp only [blockMonomial_eval]
  rw [eval_eq']
  simp only [Fintype.prod_prod_type]

theorem weighted_eval_block_expansion (p : MvPolynomial (K × A) ℝ)
    (U : K → A → ℝ) (w : K → ℝ) :
    (∏ k, w k) * eval (fun ka => U ka.1 ka.2) p =
      ∑ m ∈ p.support, p.coeff m * ∏ k, w k * eval (U k) (blockMonomial m k) := by
  rw [eval_block_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.prod_mul_distrib]
  ring

theorem blockMonomial_degree_le (p : MvPolynomial (K × A) ℝ)
    (m : (K × A) →₀ ℕ) (hm : m ∈ p.support) (k : K) :
    (blockMonomial m k).totalDegree ≤ p.totalDegree := by
  have htotal := polynomial_support_degree_le p.totalDegree p le_rfl m hm
  rw [Fintype.sum_prod_type] at htotal
  have hk : (∑ a, m (k, a)) ≤ ∑ j, ∑ a, m (j, a) :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (∑ a, m (j, a))) (Finset.mem_univ k)
  apply (totalDegree_monomial_le (blockExponent m k) (1 : ℝ)).trans
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simpa only [blockExponent_apply] using hk.trans htotal

end CausalLowerbound.PartC

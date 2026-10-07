import CausalLowerbound.PartC.BlockPolynomialExpansion
import CausalLowerbound.PartC.WeightedPolynomialMoments
import Mathlib.Algebra.MvPolynomial.Rename

/-! Tensoring arbitrary one-block polynomial functionals. This is the
algebraic operation in the multiblock moment formula; its factorization
on separated products is proved without assuming multiplicativity of
the individual functionals. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial
variable {K A : Type*} [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]

def joinBlockExponent (m : K → A →₀ ℕ) : (K × A) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun ka => m ka.1 ka.2)

@[simp] theorem joinBlockExponent_apply (m : K → A →₀ ℕ) (k : K) (a : A) :
    joinBlockExponent m (k, a) = m k a := by simp [joinBlockExponent]

@[simp] theorem blockExponent_join (m : K → A →₀ ℕ) (k : K) :
    blockExponent (joinBlockExponent m) k = m k := by
  ext a
  simp

theorem joinBlockMonomial_eval (m : K → A →₀ ℕ) (U : K × A → ℝ) :
    eval U (monomial (joinBlockExponent m) 1) =
      ∏ k, eval (fun a => U (k, a)) (monomial (m k) 1) := by
  simp only [eval_monomial, one_mul]
  simp_rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fintype.prod_prod_type, joinBlockExponent_apply]

def blockPolynomialFunctional (L : K → MvPolynomial A ℝ →ₗ[ℝ] ℝ) :
    MvPolynomial (K × A) ℝ →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun m => ∏ k, L k (blockMonomial m k))

theorem blockPolynomialFunctional_monomial (L : K → MvPolynomial A ℝ →ₗ[ℝ] ℝ)
    (m : (K × A) →₀ ℕ) (c : ℝ) :
    blockPolynomialFunctional L (monomial m c) = c * ∏ k, L k (blockMonomial m k) :=
  Finsupp.linearCombination_single ℝ c m

theorem blockPolynomialFunctional_expansion (L : K → MvPolynomial A ℝ →ₗ[ℝ] ℝ)
    (p : MvPolynomial (K × A) ℝ) :
    blockPolynomialFunctional L p = ∑ m ∈ p.support, p.coeff m * ∏ k, L k (blockMonomial m k) := rfl

theorem separated_polynomial_expansion (p : K → MvPolynomial A ℝ) :
    (∏ k, rename (fun a => (k, a)) (p k)) =
      ∑ m : (∀ k, (p k).support), C (∏ k, (p k).coeff (m k).val) *
        monomial (joinBlockExponent (fun k => (m k).val)) 1 := by
  apply MvPolynomial.funext
  intro U
  have he (k : K) : eval U (rename (fun a => (k, a)) (p k)) =
      ∑ m : (p k).support, (p k).coeff m.val * eval (fun a => U (k, a)) (monomial m.val 1) := by
    rw [eval_rename]
    rw [Finset.sum_coe_sort (p k).support
      (fun m => (p k).coeff m * eval (fun a => U (k, a)) (monomial m 1))]
    rw [eval_eq']
    simp only [eval_monomial, one_mul]
    simp_rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  rw [map_prod]
  simp_rw [he]
  rw [Fintype.prod_sum]
  simp only [map_sum, map_mul, eval_C, joinBlockMonomial_eval]
  apply Finset.sum_congr rfl
  intro m _
  exact Finset.prod_mul_distrib

theorem blockPolynomialFunctional_separated_product (L : K → MvPolynomial A ℝ →ₗ[ℝ] ℝ)
    (p : K → MvPolynomial A ℝ) :
    blockPolynomialFunctional L (∏ k, rename (fun a => (k, a)) (p k)) = ∏ k, L k (p k) := by
  rw [separated_polynomial_expansion, map_sum]
  simp only [MvPolynomial.C_mul', map_smul, smul_eq_mul, blockPolynomialFunctional_monomial,
    one_mul, blockMonomial, blockExponent_join]
  have he (k : K) : L k (p k) =
      ∑ m : (p k).support, (p k).coeff m.val * L k (monomial m.val 1) := by
    rw [polynomial_linear_expansion]
    exact (Finset.sum_coe_sort (p k).support
      (fun m => (p k).coeff m * L k (monomial m 1))).symm
  simp_rw [he]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact Finset.prod_mul_distrib.symm

end CausalLowerbound.PartC

import CausalLowerbound.PartC.BlockCoefficientShift

/-! Arbitrary tensor polynomial functionals commute with independent
coefficient shifts. The empty tensor evaluates the constant polynomial,
which also covers components with no carried blocks. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial
variable {K A V Ω : Type*} [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V] [Fintype Ω]

theorem blockPolynomialFunctional_C (L : K → MvPolynomial A ℝ →ₗ[ℝ] ℝ) (c : ℝ) :
    blockPolynomialFunctional L (C c) = c * ∏ k, L k 1 := by
  change blockPolynomialFunctional L (monomial 0 c) = _
  rw [blockPolynomialFunctional_monomial]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  congr 1
  have hm : blockExponent (0 : (K × A) →₀ ℕ) k = 0 := by
    ext a
    simp only [blockExponent_apply, Finsupp.zero_apply]
  rw [blockMonomial, hm]
  rfl

theorem blockPolynomialFunctional_isEmpty [IsEmpty K]
    (L : K → MvPolynomial A ℝ →ₗ[ℝ] ℝ) (p : MvPolynomial (K × A) ℝ) :
    blockPolynomialFunctional L p = eval (fun _ => 0) p := by
  rw [p.eq_C_of_isEmpty, blockPolynomialFunctional_C, Finset.prod_of_isEmpty, mul_one, eval_C]

theorem blockPolynomialFunctional_shift_average_general
    (μ : K → FiniteLaw Ω) (U : K → Ω → A → ℝ)
    (c : K → A → V → ℝ) (amp : K → ℝ)
    (L : K → MvPolynomial V ℝ →ₗ[ℝ] ℝ) (p : MvPolynomial (K × A) ℝ) :
    blockPolynomialFunctional (fun k => (L k).comp
      (coefficientShiftAverage (μ k) (U k) (c k) (amp k))) p =
      blockPolynomialFunctional L (blockShiftAverage μ U c amp p) := by
  let F := blockPolynomialFunctional (fun k => (L k).comp
    (coefficientShiftAverage (μ k) (U k) (c k) (amp k)))
  let H := (blockPolynomialFunctional L).comp (blockShiftAverage μ U c amp)
  have hm (m : (K × A) →₀ ℕ) : F (monomial m 1) = H (monomial m 1) := by
    dsimp only [F, H, LinearMap.comp_apply]
    rw [blockPolynomialFunctional_monomial, one_mul]
    conv_rhs => rw [monomial_separated_block_product, blockShiftAverage_separated_product,
      blockPolynomialFunctional_separated_product]
    rfl
  change F p = H p
  rw [polynomial_linear_expansion F p, polynomial_linear_expansion H p]
  apply Finset.sum_congr rfl
  intro m _
  exact congrArg (fun z : ℝ => p.coeff m * z) (hm m)

end CausalLowerbound.PartC

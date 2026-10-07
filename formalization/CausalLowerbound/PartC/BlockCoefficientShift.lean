import CausalLowerbound.PartC.BlockPatternFunctional
import CausalLowerbound.PartC.CoefficientShiftPolynomial

/-! Independent coefficient averages commute with the tensor product of
block site functionals. The equality holds for the whole polynomial,
including its constant term, rather than only for a separated input. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial
variable {K A V Ω : Type*} [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V] [Fintype Ω]

def coefficientShiftAverage (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (c : A → V → ℝ) (amp : ℝ) : MvPolynomial A ℝ →ₗ[ℝ] MvPolynomial V ℝ :=
  ∑ ω, μ.weight ω •
    (aeval (fun a => C (U ω a) + ∑ v, C (amp * c a v) * X v)).toLinearMap

theorem coefficientShiftAverage_eval (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (c : A → V → ℝ) (amp : ℝ) (p : MvPolynomial A ℝ) (z : V → ℝ) :
    eval z (coefficientShiftAverage μ U c amp p) =
      μ.expect (fun ω => eval (fun a => U ω a + ∑ v, amp * c a v * z v) p) := by
  simp only [coefficientShiftAverage, LinearMap.sum_apply, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, MvPolynomial.smul_eq_C_mul, map_sum, map_mul,
    eval_C, eval_aeval_polynomial, map_add, eval_X, FiniteLaw.expect]

theorem coefficientShiftAverage_constantCoeff (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (c : A → V → ℝ) (amp : ℝ) (p : MvPolynomial A ℝ) :
    constantCoeff (coefficientShiftAverage μ U c amp p) = μ.expect (fun ω => eval (U ω) p) := by
  rw [← eval_zero', coefficientShiftAverage_eval]
  simp only [mul_zero, Finset.sum_const_zero, add_zero]

theorem coefficientShiftPolynomial_eq_average_sub (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (c : A → V → ℝ) (amp : ℝ) (p : MvPolynomial A ℝ) :
    coefficientShiftPolynomial μ U c amp p =
      coefficientShiftAverage μ U c amp p - C (μ.expect (fun ω => eval (U ω) p)) := by
  apply MvPolynomial.funext
  intro z
  rw [coefficientShiftPolynomial_eval, map_sub, coefficientShiftAverage_eval, eval_C]

def blockShiftAverage (μ : K → FiniteLaw Ω) (U : K → Ω → A → ℝ)
    (c : K → A → V → ℝ) (amp : K → ℝ) :
    MvPolynomial (K × A) ℝ →ₗ[ℝ] MvPolynomial (K × V) ℝ :=
  ∑ ξ : K → Ω, (FiniteLaw.independent μ).weight ξ •
    (aeval (fun ka : K × A => C (U ka.1 (ξ ka.1) ka.2) +
      ∑ v, C (amp ka.1 * c ka.1 ka.2 v) * X (ka.1, v))).toLinearMap

theorem blockShiftAverage_eval (μ : K → FiniteLaw Ω) (U : K → Ω → A → ℝ)
    (c : K → A → V → ℝ) (amp : K → ℝ) (p : MvPolynomial (K × A) ℝ) (z : K × V → ℝ) :
    eval z (blockShiftAverage μ U c amp p) =
      (FiniteLaw.independent μ).expect (fun ξ => eval
        (fun ka => U ka.1 (ξ ka.1) ka.2 + ∑ v, amp ka.1 * c ka.1 ka.2 v * z (ka.1, v)) p) := by
  simp only [blockShiftAverage, LinearMap.sum_apply, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, MvPolynomial.smul_eq_C_mul, map_sum, map_mul,
    eval_C, eval_aeval_polynomial, map_add, eval_X, FiniteLaw.expect]

theorem blockShiftAverage_separated_product (μ : K → FiniteLaw Ω) (U : K → Ω → A → ℝ)
    (c : K → A → V → ℝ) (amp : K → ℝ) (p : K → MvPolynomial A ℝ) :
    blockShiftAverage μ U c amp (∏ k, rename (fun a => (k, a)) (p k)) =
      ∏ k, rename (fun v => (k, v)) (coefficientShiftAverage (μ k) (U k) (c k) (amp k) (p k)) := by
  apply MvPolynomial.funext
  intro z
  rw [blockShiftAverage_eval]
  simp only [map_prod, eval_rename, coefficientShiftAverage_eval]
  exact FiniteLaw.expect_independent_prod μ
    (fun k ω => eval (fun a => U k ω a + ∑ v, amp k * c k a v * z (k, v)) (p k))

theorem monomial_separated_block_product (m : (K × A) →₀ ℕ) :
    monomial m (1 : ℝ) = ∏ k, rename (fun a => (k, a)) (blockMonomial m k) := by
  apply MvPolynomial.funext
  intro U
  simp only [map_prod, eval_rename, eval_monomial, one_mul, blockMonomial_eval]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  rfl

theorem blockPolynomialFunctional_shift_average (μ : K → FiniteLaw Ω) (U : K → Ω → A → ℝ)
    (c : K → A → V → ℝ) (amp : K → ℝ) (w : K → Finset V → ℝ)
    (p : MvPolynomial (K × A) ℝ) :
    blockPolynomialFunctional (fun k => (sitePatternFunctional (w k)).comp
      (coefficientShiftAverage (μ k) (U k) (c k) (amp k))) p =
      sitePatternFunctional (fun S => ∏ k, w k (blockSiteSet S k)) (blockShiftAverage μ U c amp p) := by
  let L := blockPolynomialFunctional (fun k => (sitePatternFunctional (w k)).comp
    (coefficientShiftAverage (μ k) (U k) (c k) (amp k)))
  let R := (sitePatternFunctional (fun S => ∏ k, w k (blockSiteSet S k))).comp
    (blockShiftAverage μ U c amp)
  have hm (m : (K × A) →₀ ℕ) : L (monomial m 1) = R (monomial m 1) := by
    dsimp only [L, R, LinearMap.comp_apply]
    rw [blockPolynomialFunctional_monomial, one_mul]
    conv_rhs => rw [monomial_separated_block_product, blockShiftAverage_separated_product,
      sitePatternFunctional_block_product]
    rfl
  change L p = R p
  calc
    L p = ∑ m ∈ p.support, p.coeff m * L (monomial m 1) := polynomial_linear_expansion L p
    _ = ∑ m ∈ p.support, p.coeff m * R (monomial m 1) := by
      apply Finset.sum_congr rfl
      intro m _
      exact congrArg (fun a : ℝ => p.coeff m * a) (hm m)
    _ = R p := (polynomial_linear_expansion R p).symm

end CausalLowerbound.PartC

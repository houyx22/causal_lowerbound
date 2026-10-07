import CausalLowerbound.PartC.SitePolynomialFunctional

/-! The unaveraged shift of a coefficient polynomial, as a linear map to
site polynomials. Polynomial identities can therefore be applied before
the design-weighted site functional and its degree truncation. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial
variable {A K V Ω : Type*} [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype Ω]

theorem eval_aeval_polynomial (F : A → MvPolynomial V ℝ) (p : MvPolynomial A ℝ) (z : V → ℝ) :
    eval z (aeval F p) = eval (fun a => eval z (F a)) p :=
  MvPolynomial.comp_aeval_apply F (aeval z) p

def coefficientShiftPolynomial (μ : FiniteLaw Ω) (U : Ω → A → ℝ) (c : A → V → ℝ) (amp : ℝ) :
    MvPolynomial A ℝ →ₗ[ℝ] MvPolynomial V ℝ :=
  ∑ ω, μ.weight ω •
    ((aeval (fun a => C (U ω a) + ∑ i, C (amp * c a i) * X i)).toLinearMap -
      (aeval (fun a => C (U ω a) : A → MvPolynomial V ℝ)).toLinearMap)

theorem coefficientShiftPolynomial_eval (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (c : A → V → ℝ) (amp : ℝ) (p : MvPolynomial A ℝ) (z : V → ℝ) :
    eval z (coefficientShiftPolynomial μ U c amp p) =
      μ.expect (fun ω => eval (fun a => U ω a + ∑ i, amp * c a i * z i) p) -
        μ.expect (fun ω => eval (U ω) p) := by
  simp only [coefficientShiftPolynomial, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, AlgHom.toLinearMap_apply, MvPolynomial.smul_eq_C_mul,
    map_sum, map_mul, map_sub, eval_C, eval_aeval_polynomial, map_add, eval_X,
    FiniteLaw.expect, Finset.sum_sub_distrib, mul_sub]

theorem coefficientShiftPolynomial_C (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (c : A → V → ℝ) (amp b : ℝ) : coefficientShiftPolynomial μ U c amp (C b) = 0 := by
  simp only [coefficientShiftPolynomial, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, AlgHom.toLinearMap_apply, aeval_C, sub_self, smul_zero, Finset.sum_const_zero]

theorem coefficientShiftPolynomial_word (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (c : A → V → ℝ) (amp : ℝ) (a : K → A) :
    coefficientShiftPolynomial μ U c amp (∏ k, X (a k)) =
      wordShiftPolynomial μ (fun ω k => U ω (a k)) (fun k i => c (a k) i) amp := by
  apply MvPolynomial.funext
  intro z
  rw [coefficientShiftPolynomial_eval, wordShiftPolynomial_eval]
  simp only [map_prod, eval_X]

end CausalLowerbound.PartC

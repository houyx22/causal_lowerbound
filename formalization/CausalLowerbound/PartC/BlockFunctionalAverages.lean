import CausalLowerbound.PartC.BlockPolynomialFunctional
import Mathlib.MeasureTheory.Integral.Pi

/-! Move independent finite averages and actual ghost integrals through
the block polynomial functional. Integrability is checked only on the
finitely many monomials used by the input polynomial. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial
variable {K A : Type*} [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]

theorem blockPolynomialFunctional_finite_average {Ω : K → Type*} [∀ k, Fintype (Ω k)]
    (μ : ∀ k, FiniteLaw (Ω k)) (L : ∀ k, Ω k → MvPolynomial A ℝ →ₗ[ℝ] ℝ)
    (p : MvPolynomial (K × A) ℝ) :
    blockPolynomialFunctional (fun k => ∑ ω, (μ k).weight ω • L k ω) p =
      (FiniteLaw.independent μ).expect (fun ω => blockPolynomialFunctional (fun k => L k (ω k)) p) := by
  rw [blockPolynomialFunctional_expansion]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  symm
  unfold FiniteLaw.expect
  simp only [blockPolynomialFunctional_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  calc
    _ = p.coeff m * (FiniteLaw.independent μ).expect
        (fun ω => ∏ k, L k (ω k) (blockMonomial m k)) := by
      rw [FiniteLaw.expect, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = _ := congrArg (fun a : ℝ => p.coeff m * a)
      (FiniteLaw.expect_independent_prod μ (fun k ω => L k ω (blockMonomial m k)))

theorem blockPolynomialFunctional_integral {Z : K → Type*} [∀ k, MeasureSpace (Z k)]
    [∀ k, SigmaFinite (volume : Measure (Z k))]
    (L : ∀ k, Z k → MvPolynomial A ℝ →ₗ[ℝ] ℝ) (p : MvPolynomial (K × A) ℝ)
    (hL : ∀ m ∈ p.support, ∀ k, Integrable (fun z => L k z (blockMonomial m k))) :
    (∫ z : ∀ k, Z k, blockPolynomialFunctional (fun k => L k (z k)) p) =
      ∑ m ∈ p.support, p.coeff m * ∏ k, ∫ z, L k z (blockMonomial m k) := by
  simp only [blockPolynomialFunctional_expansion]
  rw [integral_finset_sum p.support (fun m hm =>
    (Integrable.fintype_prod_dep (hL m hm)).const_mul (p.coeff m))]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_const_mul]
  exact congrArg (fun a : ℝ => p.coeff m * a)
    (integral_fintype_prod_eq_prod K (fun k z => L k z (blockMonomial m k)))

end CausalLowerbound.PartC

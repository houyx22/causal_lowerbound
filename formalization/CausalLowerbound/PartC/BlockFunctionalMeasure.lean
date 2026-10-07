import CausalLowerbound.PartC.BlockFunctionalAverages

/-! The block-functional integral formulas for explicitly supplied product
measures. Each local monomial is checked for integrability before exchanging
the polynomial sum and the product integral. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial
variable {K A : Type*} [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]
variable {Z : K → Type*} [∀ k, MeasurableSpace (Z k)]

theorem blockPolynomialFunctional_integral_measure
    (μ : ∀ k, Measure (Z k)) [∀ k, SigmaFinite (μ k)]
    (L : ∀ k, Z k → MvPolynomial A ℝ →ₗ[ℝ] ℝ) (p : MvPolynomial (K × A) ℝ)
    (hL : ∀ m ∈ p.support, ∀ k, Integrable (fun z => L k z (blockMonomial m k)) (μ k)) :
    (∫ z : ∀ k, Z k, blockPolynomialFunctional (fun k => L k (z k)) p ∂Measure.pi μ) =
      ∑ m ∈ p.support, p.coeff m * ∏ k, ∫ z, L k z (blockMonomial m k) ∂μ k := by
  letI : ∀ k, MeasureSpace (Z k) := fun k => ⟨μ k⟩
  letI : ∀ k, SigmaFinite (volume : Measure (Z k)) := fun k => inferInstanceAs (SigmaFinite (μ k))
  exact blockPolynomialFunctional_integral L p hL

theorem blockPolynomialFunctional_integrable_measure
    (μ : ∀ k, Measure (Z k)) [∀ k, SigmaFinite (μ k)]
    (L : ∀ k, Z k → MvPolynomial A ℝ →ₗ[ℝ] ℝ) (p : MvPolynomial (K × A) ℝ)
    (hL : ∀ m ∈ p.support, ∀ k, Integrable (fun z => L k z (blockMonomial m k)) (μ k)) :
    Integrable (fun z : ∀ k, Z k => blockPolynomialFunctional (fun k => L k (z k)) p) (Measure.pi μ) := by
  letI : ∀ k, MeasureSpace (Z k) := fun k => ⟨μ k⟩
  letI : ∀ k, SigmaFinite (volume : Measure (Z k)) := fun k => inferInstanceAs (SigmaFinite (μ k))
  simp only [blockPolynomialFunctional_expansion]
  exact integrable_finset_sum p.support (fun m hm =>
    (Integrable.fintype_prod_dep (hL m hm)).const_mul (p.coeff m))

end CausalLowerbound.PartC

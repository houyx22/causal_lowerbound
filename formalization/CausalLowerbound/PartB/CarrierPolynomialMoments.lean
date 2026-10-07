import CausalLowerbound.PartB.PolynomialMoments
import CausalLowerbound.PartB.CarrierPosteriorMoments
import CausalLowerbound.PartB.RetainedEvaluation

/-! The concrete carrier posterior matches every coefficient polynomial
of degree at most 4Q. Evaluations of the virtual shift then discard ghost
positions before any integration is performed. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped BigOperators
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener ConfigurationShells
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d Ω K : Type*} [Fintype d] [DecidableEq d] [Fintype Ω] [Fintype K]

theorem coefficientPosterior_constant_expect (H : DiscreteLaw ℕ) (μ : FiniteLaw Ω)
    (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (u : K → Torus d) (f : Ω → ℝ) :
    (coefficientPosterior H (fun _ => μ) Q θ hθ hθ1 u).expect f = μ.expect f := by
  unfold coefficientPosterior
  rw [DiscreteLaw.mixFinite_expect]
  simp only [DiscreteLaw.expect, tsum_mul_right, DiscreteLaw.tsum_weight, one_mul]

theorem paperIdealVector_scalar (Q : ℕ) (μ : FiniteLaw Ω)
    (U : Ω → CoefficientExponent d Q → ℝ) (p B : ℝ) (n : ℕ)
    (η : MomentExponent (CoefficientExponent d Q) (4 * Q)) (u : Fin Q × d → ℝ) :
    carrierEvaluation Q (fun i => torusProjection (configurationSite u i))
      (paperIdealVector Q μ U p B n η) =
    graphTaper edgeLeft edgeRight taperCutoff (logarithmicThreshold p B (n + 1))
      (graphDistance edgeLeft edgeRight u) *
      ((μ.prod (independentSigns (ι := Fin Q))).expect (monomialFeature
        (fun z => virtualCoefficientShift (U z.1) u (polynomialAmplitude p (n + 1))
          (fun i => sign (z.2 i))) η) - μ.expect (monomialFeature U η)) := by
  change (toContinuous (paperIdealVector Q μ U p B n η) (torusProjection u)).re = _
  rw [paperIdealVector, partBIdealVector_value, Complex.ofReal_re]
  rfl

theorem paper_posterior_polynomial_interpolation (Q : ℕ) [NeZero Q] (ρ θ p B : ℝ)
    (hρ : 0 < ρ) (hθ : 0 < θ) (hθ1 : θ < 1) (hp : 0 < p)
    (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    ∀ᶠ n : ℕ in atTop, ∃ (H : DiscreteLaw ℕ)
      (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))),
      0 < H.weight 0 ∧ (∀ label z, 0 < (kernel label).weight z) ∧
      ∀ (u : Fin Q × d → ℝ) (L : MvPolynomial (CoefficientExponent d Q) ℝ),
        L.totalDegree ≤ 4 * Q →
        (coefficientPosterior H kernel Q θ hθ.le hθ1
          (fun i => torusProjection (configurationSite u i))).expect
          (fun z => MvPolynomial.eval (paperCoefficientAtoms Q ρ z) L) -
        (paperCoefficientLaw Q).expect (fun z => MvPolynomial.eval (paperCoefficientAtoms Q ρ z) L) =
        graphTaper edgeLeft edgeRight taperCutoff (logarithmicThreshold p B (n + 1))
          (graphDistance edgeLeft edgeRight u) *
          (((paperCoefficientLaw Q).prod (independentSigns (ι := Fin Q))).expect
            (fun z => MvPolynomial.eval (virtualCoefficientShift (paperCoefficientAtoms Q ρ z.1) u
              (polynomialAmplitude p (n + 1)) (fun i => sign (z.2 i))) L) -
            (paperCoefficientLaw Q).expect (fun z => MvPolynomial.eval (paperCoefficientAtoms Q ρ z) L)) := by
  filter_upwards [paper_posterior_master_moments (d := d) Q ρ θ p B hρ hθ hθ1 hp hB] with n hn
  obtain ⟨H, kernel, h0, hk, hm⟩ := hn
  refine ⟨H, kernel, h0, hk, ?_⟩
  intro u L hL
  apply polynomial_moment_interpolation (4 * Q) _ (paperCoefficientLaw Q)
    (coefficientPosterior H kernel Q θ hθ.le hθ1
      (fun i => torusProjection (configurationSite u i)))
    ((paperCoefficientLaw Q).prod (independentSigns (ι := Fin Q)))
    (paperCoefficientAtoms Q ρ) (paperCoefficientAtoms Q ρ) _ _ L hL
  intro η
  have h := hm (fun i => torusProjection (configurationSite u i)) η
  rw [coefficientPosterior_constant_expect, paperIdealVector_scalar] at h
  exact h

end CausalLowerbound.PartB.ShellGeometry

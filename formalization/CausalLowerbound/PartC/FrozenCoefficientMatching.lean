import CausalLowerbound.PartC.FrozenPropensityMatching
import CausalLowerbound.PartC.PropensityLikelihoodPolynomials

/-! The coefficient target, after averaging independent rough fields,
is the design-weighted difference of the real likelihood products. The
taper is retained, including its zero set. No carrier posterior or
independence of shared physical signs is assumed in this algebraic step. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound

theorem FiniteLaw.expect_comm {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (f : Ω → Γ → ℝ) :
    μ.expect (fun ω => ν.expect (f ω)) = ν.expect (fun γ => μ.expect (fun ω => f ω γ)) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro ω _
  ring

namespace PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial RoughPropensity
variable {d V J Ω : Type*} [Fintype d] [DecidableEq d] [Fintype V] [LinearOrder V]
  [Fintype J] [DecidableEq J] [Fintype Ω]

theorem frozen_propensity_coefficient_matching
    {Ξ : V → Type*} [∀ i, Fintype (Ξ i)]
    (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (laws : ∀ i, FiniteLaw (Ξ i)) (F : ∀ i, Ξ i → ℝ)
    (R T ja v scale offset ψ : V → ℝ)
    (hmean : ∀ i, (laws i).expect (F i) = 0)
    (hvar : ∀ i, (laws i).expect (fun ω => F i ω ^ 2) = v i)
    (W : Representative.Array d V J 1) (u : V × d → ℝ) (ζ : J → Bool) (τ amp : ℝ) :
    (FiniteLaw.independent laws).expect (fun ω =>
      propensityCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ
        (fun i => scale i ^ 2 * ja i ^ 2 * v i ^ 2) W u (fun i => scale i * F i (ω i)) ζ
        (retainedPropensityPolynomial Q R T ja (fun i => F i (ω i)) offset ψ (configurationSite u))) =
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) *
        μ.expect (fun ξ => (FiniteLaw.independent laws).expect (fun ω =>
          pointValue (torusProjection u) (fun i => scale i * F i (ω i)) ζ W *
            ((∏ i, (likelihood (R i) (T i) (ja i)
              (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)) (F i (ω i)) +
              realField (R i) (T i) (ja i) (ja i * (ψ i * amp) * scale i * v i) (F i (ω i)))) -
              ∏ i, likelihood (R i) (T i) (ja i)
                (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)) (F i (ω i))))) := by
  let law := FiniteLaw.independent laws
  let κ (i : V) := scale i ^ 2 * ja i ^ 2 * v i ^ 2
  let z (ω : ∀ i, Ξ i) (i : V) := scale i * F i (ω i)
  let smooth (ξ : Ω) (i : V) := offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)
  let a (ξ : Ω) (ω : ∀ i, Ξ i) (i : V) := likelihood (R i) (T i) (ja i) (smooth ξ i) (F i (ω i))
  let b (ω : ∀ i, Ξ i) (i : V) := increment (R i) (T i) (ja i) (ψ i * amp) (F i (ω i))
  let p (ξ : Ω) (ω : ∀ i, Ξ i) := ∏ i, (C (b ω i) * X i + C (a ξ ω i))
  let weight (ω : ∀ i, Ξ i) := pointValue (torusProjection u) (z ω) ζ W
  let g (ξ : Ω) (ω : ∀ i, Ξ i) := ∏ i, (a ξ ω i +
    realField (R i) (T i) (ja i) (ja i * (ψ i * amp) * scale i * v i) (F i (ω i)))
  let χ := graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u)
  have hp (ω : ∀ i, Ξ i) :
      propensityCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ κ W u (z ω) ζ
        (retainedPropensityPolynomial Q R T ja (fun i => F i (ω i)) offset ψ (configurationSite u)) =
      χ * μ.expect (fun ξ => propensityPolynomialFunctional κ W u (z ω) ζ (p ξ ω) -
        weight ω * ∏ i, a ξ ω i) := by
    rw [propensityCoefficientFunctional_retained Q hQ hcard μ U u τ amp id (configurationSite u)
      (fun _ => rfl) R T ja (fun i => F i (ω i)) offset ψ κ W (z ω) ζ]
    simp only [FiniteLaw.expect_sub, FiniteLaw.expect_mul]
    change χ * (μ.expect (fun ξ => propensityPolynomialFunctional κ W u (z ω) ζ (p ξ ω)) -
      μ.expect (fun ξ => ∏ i, a ξ ω i) * weight ω) = _
    ring
  have hmatch (ξ : Ω) :
      law.expect (fun ω => propensityPolynomialFunctional κ W u (z ω) ζ (p ξ ω)) =
        law.expect (fun ω => weight ω * g ξ ω) :=
    frozen_propensity_polynomial_matching laws F R T ja (fun i => ψ i * amp) v scale
      (smooth ξ) hmean hvar W u ζ
  change law.expect (fun ω =>
    propensityCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ κ W u (z ω) ζ
      (retainedPropensityPolynomial Q R T ja (fun i => F i (ω i)) offset ψ (configurationSite u))) =
    χ * μ.expect (fun ξ => law.expect (fun ω => weight ω * (g ξ ω - ∏ i, a ξ ω i)))
  simp_rw [hp]
  rw [law.expect_mul, law.expect_comm μ]
  apply congrArg (fun x : ℝ => χ * x)
  apply μ.expect_congr
  intro ξ
  rw [law.expect_sub, hmatch ξ, ← law.expect_sub]
  apply law.expect_congr
  intro ω
  ring

end PartC
end CausalLowerbound

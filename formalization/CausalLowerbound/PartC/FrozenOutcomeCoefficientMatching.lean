import CausalLowerbound.PartC.FrozenOutcomeMatching
import CausalLowerbound.PartC.FrozenCoefficientMatching

/-! The complete cubic coefficient target equals the design-weighted
real likelihood increment after independent rough-field averaging.
The Fourier--Walsh coefficients and coefficient-law draw remain fixed
through the sitewise cubic bridge. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial RoughOutcome
variable {d V J Ω : Type*} [Fintype d] [DecidableEq d] [Fintype V] [LinearOrder V]
  [Fintype J] [DecidableEq J] [Fintype Ω]

theorem frozen_outcome_coefficient_matching
    {Ξ : V → Type*} [∀ i, Fintype (Ξ i)]
    (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (laws : ∀ i, FiniteLaw (Ξ i)) (F : ∀ i, Ξ i → ℝ)
    (R T jb η v scale offset ψ : V → ℝ)
    (hmean : ∀ i, (laws i).expect (F i) = 0)
    (hvar : ∀ i, (laws i).expect (fun ω => F i ω ^ 2) = v i)
    (hthird : ∀ i, (laws i).expect (fun ω => F i ω ^ 3) = 0)
    (W : Representative.Array d V J 3) (u : V × d → ℝ) (ζ : J → Bool) (τ amp : ℝ)
    (hcorrection : ∀ i, (((ψ i * amp) * scale i) * jb i * v i) * η i =
      ((ψ i * amp) * scale i) ^ 3 * jb i * (laws i).expect (fun ω => F i ω ^ 4)) :
    (FiniteLaw.independent laws).expect (fun ω =>
      outcomeCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ
        (fun i => scale i ^ 2 * v i) W u (fun i => scale i * F i (ω i)) ζ
        (retainedOutcomePolynomial Q R T jb η (fun i => F i (ω i)) offset ψ (configurationSite u))) =
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) *
        μ.expect (fun ξ => (FiniteLaw.independent laws).expect (fun ω =>
          pointValue (torusProjection u) (fun i => scale i * F i (ω i)) ζ W *
            ((∏ i, (likelihood (R i) (T i) (jb i) (η i)
              (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)) (F i (ω i)) +
              realField (R i) (T i)
                (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i))
                (((ψ i * amp) * scale i) * jb i * v i))) -
              ∏ i, likelihood (R i) (T i) (jb i) (η i)
                (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)) (F i (ω i))))) := by
  let law := FiniteLaw.independent laws
  let κ (i : V) := scale i ^ 2 * v i
  let z (ω : ∀ i, Ξ i) (i : V) := scale i * F i (ω i)
  let smooth (ξ : Ω) (i : V) := offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)
  let a (ξ : Ω) (ω : ∀ i, Ξ i) (i : V) := likelihood (R i) (T i) (jb i) (η i) (smooth ξ i) (F i (ω i))
  let p (ξ : Ω) (ω : ∀ i, Ξ i) := ∏ i, outcomeTaylorPolynomial (R i) (T i) (ψ i * amp)
    (jb i) (η i) (smooth ξ i) (F i (ω i)) (X i)
  let weight (ω : ∀ i, Ξ i) := pointValue (torusProjection u) (z ω) ζ W
  let g (ξ : Ω) (ω : ∀ i, Ξ i) := ∏ i, (a ξ ω i +
    realField (R i) (T i) (smooth ξ i) (((ψ i * amp) * scale i) * jb i * v i))
  let χ := graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u)
  have hp (ω : ∀ i, Ξ i) :
      outcomeCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ κ W u (z ω) ζ
        (retainedOutcomePolynomial Q R T jb η (fun i => F i (ω i)) offset ψ (configurationSite u)) =
      χ * μ.expect (fun ξ => outcomePolynomialFunctional κ W u (z ω) ζ (p ξ ω) -
        weight ω * ∏ i, a ξ ω i) := by
    rw [outcomeCoefficientFunctional_retained Q hQ hcard μ U u τ amp id (configurationSite u)
      (fun _ => rfl) R T jb η (fun i => F i (ω i)) offset ψ κ W (z ω) ζ]
    simp only [FiniteLaw.expect_sub, FiniteLaw.expect_mul]
    change χ * (μ.expect (fun ξ => outcomePolynomialFunctional κ W u (z ω) ζ (p ξ ω)) -
      μ.expect (fun ξ => ∏ i, a ξ ω i) * weight ω) = _
    ring
  have hmatch (ξ : Ω) :
      law.expect (fun ω => outcomePolynomialFunctional κ W u (z ω) ζ (p ξ ω)) =
        law.expect (fun ω => weight ω * g ξ ω) :=
    frozen_outcome_polynomial_matching laws F R T (fun i => ψ i * amp) jb η v scale
      (smooth ξ) hmean hvar hthird hcorrection W u ζ
  change law.expect (fun ω =>
    outcomeCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ κ W u (z ω) ζ
      (retainedOutcomePolynomial Q R T jb η (fun i => F i (ω i)) offset ψ (configurationSite u))) =
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

end CausalLowerbound.PartC

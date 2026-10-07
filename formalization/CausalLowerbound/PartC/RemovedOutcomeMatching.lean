import CausalLowerbound.PartC.FrozenOutcomeCoefficientMatching
import CausalLowerbound.PartC.OutcomeRemovalEvaluation
import CausalLowerbound.PartC.RemovedPropensityMatching

/-! Cubic coefficient matching under the original shared-sign law.
Only the local explicit Walsh symbols are removed. All remaining sign
dependence is retained while disjoint local fields are resampled. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative RoughOutcome
variable {V J : Type*} [Fintype V] [LinearOrder V] [Fintype J] [DecidableEq J]

theorem removed_outcome_coefficient_matching
    {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]
    (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (localSigns : V → Finset J) (hS : ∀ i j, i ≠ j → Disjoint (localSigns i) (localSigns j))
    (F : V → (J → Bool) → ℝ)
    (hF : ∀ i ζ ζ', (∀ j ∈ localSigns i, ζ j = ζ' j) → F i ζ = F i ζ')
    (R T jb η v scale offset ψ : V → ℝ)
    (hmean : ∀ i, independentSigns.expect (F i) = 0)
    (hvar : ∀ i, independentSigns.expect (fun ζ => F i ζ ^ 2) = v i)
    (hthird : ∀ i, independentSigns.expect (fun ζ => F i ζ ^ 3) = 0)
    (W : Representative.Array d V J 3) (u : V × d → ℝ) (τ amp : ℝ)
    (hcorrection : ∀ i, (((ψ i * amp) * scale i) * jb i * v i) * η i =
      ((ψ i * amp) * scale i) ^ 3 * jb i * independentSigns.expect (fun ζ => F i ζ ^ 4)) :
    let B := remove (Finset.univ.biUnion localSigns) W
    independentSigns.expect (fun ζ =>
      outcomeCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ
        (fun i => scale i ^ 2 * v i) B u (fun i => scale i * F i ζ) ζ
        (retainedOutcomePolynomial Q R T jb η (fun i => F i ζ) offset ψ (configurationSite u))) =
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) *
        μ.expect (fun ξ => independentSigns.expect (fun ζ =>
          pointValue (torusProjection u) (fun i => scale i * F i ζ) ζ B *
            ((∏ i, (likelihood (R i) (T i) (jb i) (η i)
              (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)) (F i ζ) +
              realField (R i) (T i)
                (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i))
                (((ψ i * amp) * scale i) * jb i * v i))) -
              ∏ i, likelihood (R i) (T i) (jb i) (η i)
                (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)) (F i ζ)))) := by
  let S := Finset.univ.biUnion localSigns
  let B := remove S W
  let κ (i : V) := scale i ^ 2 * v i
  let z (v : V → ℝ) (i : V) := scale i * v i
  let smooth (ξ : Ω) (i : V) := offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)
  let χ := graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u)
  let g (ζ : J → Bool) (values : V → ℝ) :=
    outcomeCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ κ B u (z values) ζ
      (retainedOutcomePolynomial Q R T jb η values offset ψ (configurationSite u))
  let h (ζ : J → Bool) (values : V → ℝ) := χ * μ.expect (fun ξ =>
    pointValue (torusProjection u) (z values) ζ B *
      ((∏ i, (likelihood (R i) (T i) (jb i) (η i) (smooth ξ i) (values i) +
        realField (R i) (T i) (smooth ξ i) (((ψ i * amp) * scale i) * jb i * v i))) -
        ∏ i, likelihood (R i) (T i) (jb i) (η i) (smooth ξ i) (values i)))
  have hout (ζ ζ' : J → Bool) (hs : ∀ j, (∀ i, j ∉ localSigns i) → ζ j = ζ' j) :
      ∀ j ∉ S, ζ j = ζ' j := by
    intro j hj
    apply hs j
    intro i hi
    exact hj (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩)
  have hg : ∀ ζ ζ' values, (∀ j, (∀ i, j ∉ localSigns i) → ζ j = ζ' j) →
      g ζ values = g ζ' values := by
    intro ζ ζ' values hs
    exact outcomeCoefficientFunctional_remove_congr S edgeLeft edgeRight μ U polynomialBasisDegree
      amp τ κ W u (z values) ζ ζ' (hout ζ ζ' hs) _
  have hh : ∀ ζ ζ' values, (∀ j, (∀ i, j ∉ localSigns i) → ζ j = ζ' j) →
      h ζ values = h ζ' values := by
    intro ζ ζ' values hs
    apply congrArg (fun x : ℝ => χ * x)
    apply μ.expect_congr
    intro ξ
    rw [pointValue_remove_congr S W (torusProjection u) (z values) ζ ζ' (hout ζ ζ' hs)]
  have hm (base : J → Bool) :
      (FiniteLaw.independent (fun _ : V => independentSigns (ι := J))).expect
        (fun fresh => g base (fun i => F i (fresh i))) =
      (FiniteLaw.independent (fun _ : V => independentSigns (ι := J))).expect
        (fun fresh => h base (fun i => F i (fresh i))) := by
    conv_rhs =>
      dsimp only [h]
      rw [FiniteLaw.expect_mul, FiniteLaw.expect_comm _ μ]
    exact frozen_outcome_coefficient_matching Q hQ hcard μ U
      (fun _ : V => independentSigns (ι := J)) F R T jb η v scale offset ψ hmean hvar hthird B u base τ amp hcorrection
  have he := disjoint_sign_matching localSigns hS F hF g h hg hh hm
  change independentSigns.expect (fun ζ => g ζ (fun i => F i ζ)) = _
  rw [he]
  conv_lhs =>
    dsimp only [h]
    rw [FiniteLaw.expect_mul, FiniteLaw.expect_comm _ μ]

end CausalLowerbound.PartC

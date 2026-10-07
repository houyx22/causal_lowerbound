import CausalLowerbound.PartC.LocalSignResampling
import CausalLowerbound.PartC.PropensityRemovalEvaluation
import CausalLowerbound.PartC.FrozenCoefficientMatching

/-! Exact coefficient matching under the original shared sign law after
removing the local Walsh symbols. The local fields use disjoint symbol
sets; the remaining coefficient dependence is preserved and averaged. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative RoughPropensity
section Resampling
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

theorem disjoint_sign_matching {A : Type*} (S : V → Finset J)
    (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (F : V → (J → Bool) → A)
    (hF : ∀ i ζ ζ', (∀ j ∈ S i, ζ j = ζ' j) → F i ζ = F i ζ')
    (g h : (J → Bool) → (V → A) → ℝ)
    (hg : ∀ ζ ζ' v, (∀ j, (∀ i, j ∉ S i) → ζ j = ζ' j) → g ζ v = g ζ' v)
    (hh : ∀ ζ ζ' v, (∀ j, (∀ i, j ∉ S i) → ζ j = ζ' j) → h ζ v = h ζ' v)
    (hm : ∀ base, (FiniteLaw.independent (fun _ : V => independentSigns (ι := J))).expect
      (fun fresh => g base (fun i => F i (fresh i))) =
      (FiniteLaw.independent (fun _ : V => independentSigns (ι := J))).expect
        (fun fresh => h base (fun i => F i (fresh i)))) :
    independentSigns.expect (fun ζ => g ζ (fun i => F i ζ)) =
      independentSigns.expect (fun ζ => h ζ (fun i => F i ζ)) := by
  rw [disjoint_sign_resampling S hS F g hF hg, disjoint_sign_resampling S hS F h hF hh]
  exact FiniteLaw.expect_congr _ hm

end Resampling
variable {V J : Type*} [Fintype V] [LinearOrder V] [Fintype J] [DecidableEq J]

theorem removed_propensity_coefficient_matching
    {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]
    (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (localSigns : V → Finset J) (hS : ∀ i j, i ≠ j → Disjoint (localSigns i) (localSigns j))
    (F : V → (J → Bool) → ℝ)
    (hF : ∀ i ζ ζ', (∀ j ∈ localSigns i, ζ j = ζ' j) → F i ζ = F i ζ')
    (R T ja v scale offset ψ : V → ℝ)
    (hmean : ∀ i, independentSigns.expect (F i) = 0)
    (hvar : ∀ i, independentSigns.expect (fun ζ => F i ζ ^ 2) = v i)
    (W : Representative.Array d V J 1) (u : V × d → ℝ) (τ amp : ℝ) :
    let B := remove (Finset.univ.biUnion localSigns) W
    independentSigns.expect (fun ζ =>
      propensityCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ
        (fun i => scale i ^ 2 * ja i ^ 2 * v i ^ 2) B u (fun i => scale i * F i ζ) ζ
        (retainedPropensityPolynomial Q R T ja (fun i => F i ζ) offset ψ (configurationSite u))) =
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) *
        μ.expect (fun ξ => independentSigns.expect (fun ζ =>
          pointValue (torusProjection u) (fun i => scale i * F i ζ) ζ B *
            ((∏ i, (likelihood (R i) (T i) (ja i)
              (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)) (F i ζ) +
              realField (R i) (T i) (ja i) (ja i * (ψ i * amp) * scale i * v i) (F i ζ))) -
              ∏ i, likelihood (R i) (T i) (ja i)
                (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)) (F i ζ)))) := by
  let S := Finset.univ.biUnion localSigns
  let B := remove S W
  let κ (i : V) := scale i ^ 2 * ja i ^ 2 * v i ^ 2
  let z (v : V → ℝ) (i : V) := scale i * v i
  let smooth (ξ : Ω) (i : V) := offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)
  let χ := graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u)
  let g (ζ : J → Bool) (values : V → ℝ) :=
    propensityCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ κ B u (z values) ζ
      (retainedPropensityPolynomial Q R T ja values offset ψ (configurationSite u))
  let h (ζ : J → Bool) (values : V → ℝ) := χ * μ.expect (fun ξ =>
    pointValue (torusProjection u) (z values) ζ B *
      ((∏ i, (likelihood (R i) (T i) (ja i) (smooth ξ i) (values i) +
        realField (R i) (T i) (ja i) (ja i * (ψ i * amp) * scale i * v i) (values i))) -
        ∏ i, likelihood (R i) (T i) (ja i) (smooth ξ i) (values i)))
  have hout (ζ ζ' : J → Bool) (hs : ∀ j, (∀ i, j ∉ localSigns i) → ζ j = ζ' j) :
      ∀ j ∉ S, ζ j = ζ' j := by
    intro j hj
    apply hs j
    intro i hi
    exact hj (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩)
  have hg : ∀ ζ ζ' values, (∀ j, (∀ i, j ∉ localSigns i) → ζ j = ζ' j) →
      g ζ values = g ζ' values := by
    intro ζ ζ' values hs
    exact propensityCoefficientFunctional_remove_congr S edgeLeft edgeRight μ U polynomialBasisDegree
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
    exact frozen_propensity_coefficient_matching Q hQ hcard μ U
      (fun _ : V => independentSigns (ι := J)) F R T ja v scale offset ψ hmean hvar B u base τ amp
  have he := disjoint_sign_matching localSigns hS F hF g h hg hh hm
  change independentSigns.expect (fun ζ => g ζ (fun i => F i ζ)) = _
  rw [he]
  conv_lhs =>
    dsimp only [h]
    rw [FiniteLaw.expect_mul, FiniteLaw.expect_comm _ μ]

end CausalLowerbound.PartC

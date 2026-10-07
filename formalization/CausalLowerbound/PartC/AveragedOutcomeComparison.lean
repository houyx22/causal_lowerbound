import CausalLowerbound.PartC.OutcomeObservationComparison
import CausalLowerbound.PartC.AveragedPropensityComparison
import CausalLowerbound.PartC.RawOutcomeExpansion

/-! Average the complete cubic comparison over the fixed paper coefficient
law. Its error budget is independent of the coefficient realization. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem physical_outcome_pattern_average_bound
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ a jb t τ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hc : 0 < c)
    (hw : 0 < w) (hw1 : w ≤ 1) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hidentity : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1) (hshift : 0 ≤ a * t) (hsjb : a * t ≤ jb)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (hB : ∀ k, ‖B k‖ ≤ 2) (hreflect : ∀ k, reflection (B k) = B k)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (hsmooth : ∀ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    |independentSigns.expect (fun ζ => outcomeObservationPatternSum Q hQ ρ S x₀ ℓ r h c w N a jb t τ B ζ x y G e) -
      independentSigns.expect (fun ζ => (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)).expect (fun ξ =>
        (∏ k, outcomeObservationPatternWeight false Q S x₀ ℓ r h c w N τ B x G e ζ ζ k 0) *
          ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
            (mixedOutcomeCellPolynomial Q true S x₀ ℓ r h a jb t ζ (x i) (y i))))| ≤
      outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G e := by
  let f := fun ζ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) =>
    outcomeObservationValue true Q hQ S x₀ ℓ r h c w N jb (a * t) τ B x y
      (fun i => a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))) G e ζ ζ
  let g := fun ζ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) =>
    (∏ k, outcomeObservationPatternWeight false Q S x₀ ℓ r h c w N τ B x G e ζ ζ k 0) *
      eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (mixedOutcomeComponentPolynomial Q true S x₀ ℓ r h a jb t ζ x y)
  have he ξ : |independentSigns.expect (fun ζ => f ζ ξ) - independentSigns.expect (fun ζ => g ζ ξ)| ≤
      outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G e :=
    physical_outcome_observation_comparison_bound Q hQ S (fun k => paperCoefficientAtoms Q ρ (ξ k))
      x₀ ℓ r h c w N N₀ a jb t τ hℓ hr hh hc hw hw1 hN₀ hN hm hidentity hrough
        hjb hsmall hshift hsjb x y (hsmooth ξ) hsep hcover htr B hB hreflect G e
  have hb := double_average_comparison_bound independentSigns
    (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)) f g
    (fun _ => outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G e) he
  simpa only [FiniteLaw.expect_const, f, g, outcomeObservationValue, outcomeObservationPatternSum,
    outcomeObservationPatternWeight, if_pos rfl, if_true, Bool.false_eq_true, if_false,
    mixedOutcomeComponentPolynomial, map_prod] using hb

end CausalLowerbound.PartC

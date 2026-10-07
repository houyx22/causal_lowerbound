import CausalLowerbound.PartC.OutcomeVectorTarget
import CausalLowerbound.PartB.MomentSupport

/-! The cubic target for the complete coefficient basis and all
nonconstant coefficient moments through degree 4Q on the finite grid. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def paperOutcomeTargetValue {J : Type*} [Fintype J] [DecidableEq J] (Q : ℕ) (ρ amp t : ℝ)
    (k : Fin Q → Fourier (Fin Q × d)) (v : Representative.Array d (Fin Q) J 3)
    (η : MomentExponent (CoefficientExponent d Q) (4 * Q))
    (u : Fin Q × d → ℝ) (z : Fin Q → ℝ) (ζ : J → Bool) : ℝ :=
  symmetricOutcomeChoiceValue edgeLeft edgeRight (paperCoefficientLaw Q)
    (fun ω (j : MomentPositions η) => paperCoefficientAtoms Q ρ ω j.1)
    (fun j : MomentPositions η => polynomialBasisDegree j.1) amp t k v u z ζ

theorem exists_paperOutcomeTarget (Q : ℕ) (ρ : ℝ) :
    ∃ C ≥ 0, ∀ (J : Type*) [Fintype J] [DecidableEq J], ∀ amp ≥ 0, ∀ t > 0,
      ∀ L ≥ 1, ∀ (k : Fin Q → Fourier (Fin Q × d)) (hk : ∀ i, ‖k i‖ ≤ L),
      ∃ T : Representative.Array d (Fin Q) J 3 →L[ℝ]
          (MomentExponent (CoefficientExponent d Q) (4 * Q) → Representative.Array d (Fin Q) J 3),
        (∀ v, ‖T v‖ ≤ ((C * ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Q.choose 2 *
          ∑ j ∈ Finset.Icc 1 (4 * Q), (amp / t) ^ j) * L ^ Q) * ‖v‖) ∧
        (∀ v i x z ζ (σ : Equiv.Perm (Fin Q)),
          pointValue (permuteSlots σ x) (fun j => z (σ j)) ζ (T v i) = pointValue x z ζ (T v i)) ∧
        (∀ v i S, remove S (T v i) = T (remove S v) i) ∧
        ∀ v i u z ζ, (∀ u i, (toContinuous (k i) (torusProjection u)).im = 0) →
          pointValue (torusProjection u) z ζ (T v i) = paperOutcomeTargetValue Q ρ amp t k v i u z ζ := by
  simpa only [paperOutcomeTargetValue, completeEdge_card, Fintype.card_fin] using
    exists_outcomeVectorTarget (V := Fin Q) edgeLeft edgeRight (paperCoefficientLaw Q)
      (fun (η : MomentExponent (CoefficientExponent d Q) (4 * Q)) ω (j : MomentPositions η) =>
        paperCoefficientAtoms Q ρ ω j.1)
      (fun η (j : MomentPositions η) => polynomialBasisDegree j.1) (4 * Q) momentPositions_card

theorem paper_outcome_moment_radius (Q : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ radius > 0, ∀ v : MomentExponent (CoefficientExponent d Q) (4 * Q) → ℝ,
      (∀ i, |v i| ≤ radius) → ∃ ν : FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)),
        (∀ y, 0 < ν.weight y) ∧ ∀ i,
          ν.expect (monomialFeature (paperCoefficientAtoms Q ρ) i) =
            (paperCoefficientLaw Q).expect (monomialFeature (paperCoefficientAtoms Q ρ) i) + v i :=
  (moment_simplex_in_ball (4 * Q) (0 : CoefficientExponent d Q → ℝ) ρ hρ).2.2

end CausalLowerbound.PartC

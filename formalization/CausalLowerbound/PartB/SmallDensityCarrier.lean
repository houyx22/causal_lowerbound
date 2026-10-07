import CausalLowerbound.PartB.MomentSupport

/-! The carrier works with an arbitrarily small positive density contrast,
as required by the prescribed two-sided design bounds. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem paper_positiveCarrier_contrast (Q : ℕ) [NeZero Q] (ρ θ : ℝ)
    (hρ : 0 < ρ) (hθ : 0 < θ) (p B : ℝ) (hp : 0 < p)
    (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    ∀ᶠ n in atTop,
      HasPositiveCarrier 1 (PositiveWiener.naturalAtom (d := d) (ι := Fin Q) θ)
        (multiplicationIncrement
          (paperIdealVector Q (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ) p B n))
        (monomialFeature (paperCoefficientAtoms Q ρ)) (paperCoefficientLaw Q) := by
  let J := paperIdealVector Q (paperCoefficientLaw Q) (paperCoefficientAtoms (d := d) Q ρ) p B
  let P := PositiveWiener.carrierPolarization (d := d) (ι := Fin Q)
    (I := MomentExponent (CoefficientExponent d Q) (4 * Q)) θ hθ
  have hJ : Tendsto (fun n => ‖J n‖) atTop (𝓝 0) := by
    exact partB_wiener_vanishes Q (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ)
      polynomialBasisDegree p B hp hB
  exact P.eventually_hasPositiveCarrier
    (mul_nonneg (Nat.cast_nonneg _) (PositiveWiener.polarizationBound_nonneg θ))
    (by positivity) (by simp)
    (fun n => multiplicationIncrement (J n)) (fun n => ‖J n‖) (fun _ => norm_nonneg _) hJ
    (fun n D => multiplicationIncrement_bound (J n) ‖J n‖ (norm_nonneg _) le_rfl D)
    (monomialFeature (paperCoefficientAtoms Q ρ)) (paperCoefficientLaw Q)
    (gridLaw_weight_pos (4 * Q)) (smallGridRightInverse (4 * Q) 0 ρ hρ)
end CausalLowerbound.PartB.ShellGeometry

import CausalLowerbound.PartC.TaperedSiteFunctional
import CausalLowerbound.PartC.PhysicalPropensityProjectivity
import CausalLowerbound.PartC.CarrierPermutationSymmetry

/-! The full physical carrier moment, including its baseline, is the
permutation average of the tapered site functionals. Its symmetry comes
from the actual carrier atom series. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem physical_propensity_full_pattern_functional
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N θ ja t τ : ℝ) (H : DiscreteLaw ℕ)
    (B : Representative.Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (hseries : HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom unit
      (pairedAtom reflection (naturalPhysicalAtom (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ)) n) B)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : Fin Q × d → ℝ)
    (p : MvPolynomial (CoefficientExponent d Q) ℝ) :
    (paperCoefficientLaw Q).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p) *
        physicalCarrierValue x₀ ℓ r h k c w N B ζ u +
      physicalPropensityIncrementValue Q ρ x₀ ℓ r h k c w N ja t τ B ζ p u =
      (Fintype.card (Equiv.Perm (Fin Q)) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin Q),
        sitePatternFunctional (taperedPatternWeight
          (graphTaper edgeLeft edgeRight taperCutoff τ
            (graphDistance edgeLeft edgeRight (fun v => u (σ v.1, v.2))))
          (propensityPatternWeight
            (physicalPropensitySlotCorrection x₀ r h k c w N ja (fun v => u (σ v.1, v.2))) B
            (fun v => u (σ v.1, v.2))
            (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u (σ j, a))) ζ))
          (coefficientShiftAverage (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ)
            (fun a v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree a)
              (fun v => u (σ v.1, v.2))) (t * N) p) := by
  let z := fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u (j, a))
  have hsym (σ : Equiv.Perm (Fin Q)) :
      pointValue (torusProjection (fun v => u (σ v.1, v.2))) (fun j => z (σ j)) ζ B =
        physicalCarrierValue x₀ ℓ r h k c w N B ζ u :=
    carrier_series_value_symmetric x₀ ℓ r h k c w N θ H B hseries (torusProjection u) z ζ σ
  have hterm (σ : Equiv.Perm (Fin Q)) :=
    taperedSiteFunctional_shift_average (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ)
      (fun a v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree a)
        (fun v => u (σ v.1, v.2))) (t * N)
      (graphTaper edgeLeft edgeRight taperCutoff τ
        (graphDistance edgeLeft edgeRight (fun v => u (σ v.1, v.2))))
      (propensityPatternWeight
        (physicalPropensitySlotCorrection x₀ r h k c w N ja (fun v => u (σ v.1, v.2))) B
        (fun v => u (σ v.1, v.2)) (fun j => z (σ j)) ζ) p
  simp only [propensityPatternWeight_empty, hsym] at hterm
  dsimp only [z] at hterm
  simp_rw [hterm]
  simp only [physicalPropensityIncrementValue, paperPhysicalPropensityPolynomial,
    propensityCoefficientFunctional, propensityPolynomialFunctional, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, smul_eq_mul,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card (Equiv.Perm (Fin Q)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hn]
  <;> ring

end CausalLowerbound.PartC

import CausalLowerbound.PartC.PhysicalOutcomePolynomial
import CausalLowerbound.PartC.PhysicalFullMomentFunctional

/-! The complete cubic coefficient moment, including its baseline. This
linear functional is the actual moment of the positive outcome carrier. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def physicalOutcomeFullFunctional (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N t τ : ℝ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : Fin Q × d → ℝ) :
    MvPolynomial (CoefficientExponent d Q) ℝ →ₗ[ℝ] ℝ :=
  physicalCarrierValue x₀ ℓ r h k c w N B ζ u •
    coefficientExpectation (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ) +
      paperPhysicalOutcomePolynomial Q ρ x₀ r h k c w N t τ B u
        (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (configurationSite u i)) ζ

theorem physicalOutcomeFullFunctional_apply (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ)
    (k : d → ℤ) (c w N t τ : ℝ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : Fin Q × d → ℝ)
    (p : MvPolynomial (CoefficientExponent d Q) ℝ) :
    physicalOutcomeFullFunctional Q ρ x₀ ℓ r h k c w N t τ B ζ u p =
      (paperCoefficientLaw Q).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p) *
        physicalCarrierValue x₀ ℓ r h k c w N B ζ u +
          paperPhysicalOutcomePolynomial Q ρ x₀ r h k c w N t τ B u
            (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (configurationSite u i)) ζ p := by
  simp only [physicalOutcomeFullFunctional, LinearMap.add_apply, LinearMap.smul_apply,
    coefficientExpectation_apply, smul_eq_mul]
  rw [mul_comm]

end CausalLowerbound.PartC

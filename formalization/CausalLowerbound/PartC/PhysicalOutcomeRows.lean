import CausalLowerbound.PartC.SharedOutcomeRows
import CausalLowerbound.PartC.PhysicalLocalOutcomeMatching

/-! Multi-block row matching for the actual physical rough field.
Separation supplies disjoint local signs, and all four moment conditions
are derived from the actual finite packet field and its correction. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry MvPolynomial Representative RoughOutcome
variable {I K d : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  [Fintype d] [DecidableEq d]

theorem physical_outcome_polynomial_coefficient_matching
    {Rows : K → Type*} [∀ k, Fintype (Rows k)]
    (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h) (x : I → d → ℝ)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (coeff : (activeBlocks (d := d) ℓ h → Bool) → ∀ k, Rows k → ℝ)
    (degree : ∀ k, Rows k → I → Fin 4)
    (hcoeff : ∀ ζ ζ',
      (∀ j, (∀ i, j ∉ physicalLocalSigns x₀ ℓ h (x i)) → ζ j = ζ' j) → coeff ζ = coeff ζ')
    (R T jb jitter smooth : I → ℝ) (shift scale : I → K → ℝ) (owner : I → K)
    (hscale : ∀ i k, k ≠ owner i → scale i k = 0)
    (hshift : ∀ i, coarseBump x₀ h (x i) = 0 ∨
      shift i (owner i) * scale i (owner i) = 0 ∨
      shift i (owner i) * scale i (owner i) = jitter i) :
    let rough := fun i ζ => physicalRoughField x₀ ℓ h ζ (x i)
    let η := fun i => physicalRoughCorrection x₀ ℓ h (jitter i) (x i)
    let v := fun i => coarseBump x₀ h (x i) ^ 2
    independentSigns.expect (fun ζ =>
      cubicSiteFunctional (fun e => ∏ k, ∑ r, coeff ζ k r * ∏ i,
        if e (k, i) = 0 then (scale i k * rough i ζ) ^ (degree k r i).val else
          Representative.outcomeMoment (scale i k ^ 2 * v i) (degree k r i) * (scale i k * rough i ζ) ^ (e (k, i)).val)
        (∏ i, rename (fun k => (k, i))
          (outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i ζ)
            (∑ k, C (shift i k) * X k)))) =
      independentSigns.expect (fun ζ =>
        (∏ k, ∑ r, coeff ζ k r * ∏ i, (scale i k * rough i ζ) ^ (degree k r i).val) *
          ∏ i, (likelihood (R i) (T i) (jb i) (η i) (smooth i) (rough i ζ) +
            realField (R i) (T i) (smooth i) ((shift i (owner i) * scale i (owner i)) * jb i * v i))) := by
  exact shared_outcome_polynomial_coefficient_matching
    (fun i => physicalLocalSigns x₀ ℓ h (x i))
    (fun i j hij => physicalLocalSigns_disjoint x₀ ℓ h hℓ (x i) (x j) (hsep i j hij))
    (fun i ζ => physicalRoughField x₀ ℓ h ζ (x i))
    (fun i ζ ζ' he => physicalRoughField_local_congr x₀ ℓ h (x i) ζ ζ' he)
    coeff degree hcoeff R T jb (fun i => physicalRoughCorrection x₀ ℓ h (jitter i) (x i))
    (fun i => coarseBump x₀ h (x i) ^ 2) smooth shift scale owner hscale
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).1)
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).2.1)
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).2.2.1)
    (fun i => physicalRoughCorrection_zero_or_shift x₀ ℓ h
      (shift i (owner i) * scale i (owner i)) (jitter i) (jb i) hℓ hh (x i) (hshift i))

end CausalLowerbound.PartC

import CausalLowerbound.PartC.MixedOutcomeControl
import CausalLowerbound.PartC.CodedModelLegality

/-! Actual parameter functions for both mixed cases. These are connected
pointwise to the coded likelihoods and have the prescribed target value. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def roughPropensityFields {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h ja b t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) : NuisanceFields d :=
  codedFields side (fun x => ja * physicalRoughField x₀ ℓ h ζ x)
    (fun x => b * normalizedPropensityOutcome side S U x₀ r h ja t x)
    (targetField x₀ h (ja * b * t))

def roughOutcomeFields {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h a jb t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) : NuisanceFields d :=
  codedFields side (fun x => a * carriedField S U x₀ r x)
    (fun x => jb * normalizedRoughOutcome side S U x₀ ℓ r h a (a * t) ζ x)
    (targetField x₀ h (a * t * jb))

theorem roughPropensityFields_smooth {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h ja b t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    let F := roughPropensityFields side S U x₀ ℓ r h ja b t ζ
    ContDiff ℝ ∞ F.propensity ∧ ContDiff ℝ ∞ F.baseline ∧ ContDiff ℝ ∞ F.effect :=
  codedFields_smooth side _ _ _ (contDiff_const.mul (physicalRoughField_smooth _ _ _ _))
    (contDiff_const.mul (normalizedPropensityOutcome_smooth _ _ _ _ _ _ _ _))
    (contDiff_const.mul ((rescaled_smooth _ quadraticPartition_smooth _ _).pow 2))

theorem roughOutcomeFields_smooth {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h a jb t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    let F := roughOutcomeFields side S U x₀ ℓ r h a jb t ζ
    ContDiff ℝ ∞ F.propensity ∧ ContDiff ℝ ∞ F.baseline ∧ ContDiff ℝ ∞ F.effect :=
  codedFields_smooth side _ _ _ (contDiff_const.mul (carriedField_smooth _ _ _ _))
    (contDiff_const.mul (normalizedRoughOutcome_smooth _ _ _ _ _ _ _ _ _ _))
    (contDiff_const.mul ((rescaled_smooth _ quadraticPartition_smooth _ _).pow 2))

theorem roughPropensityFields_effect_center {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h ja b t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    (roughPropensityFields side S U x₀ ℓ r h ja b t ζ).effect x₀ =
      if side then ja * b * t else 0 := by
  simp only [roughPropensityFields, codedFields, targetField_center]

theorem roughOutcomeFields_effect_center {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h a jb t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    (roughOutcomeFields side S U x₀ ℓ r h a jb t ζ).effect x₀ =
      if side then a * t * jb else 0 := by
  simp only [roughOutcomeFields, codedFields, targetField_center]

theorem roughPropensityFields_likelihood {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h ja b t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (R T : ℝ) (x : d → ℝ) :
    let F := roughPropensityFields side S U x₀ ℓ r h ja b t ζ
    codedLikelihood R T (2 * F.propensity x - 1) (2 * F.baseline x - 1) (F.effect x) =
      RoughPropensity.likelihood R T ja (b * carriedField S U x₀ r x) (physicalRoughField x₀ ℓ h ζ x) +
        if side then RoughPropensity.realField R T ja (targetField x₀ h (ja * b * t) x)
          (physicalRoughField x₀ ℓ h ζ x) else 0 := by
  cases side <;>
    simp only [roughPropensityFields, codedFields, normalizedPropensityOutcome,
      Bool.false_eq_true, if_false, if_true, targetField, codedLikelihood,
      RoughPropensity.likelihood, RoughPropensity.realField] <;> ring

theorem roughOutcomeFields_likelihood {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h a jb t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (R T : ℝ) (x : d → ℝ) :
    let F := roughOutcomeFields side S U x₀ ℓ r h a jb t ζ
    codedLikelihood R T (2 * F.propensity x - 1) (2 * F.baseline x - 1) (F.effect x) =
      RoughOutcome.likelihood R T jb (physicalRoughCorrection x₀ ℓ h (a * t) x)
        (a * carriedField S U x₀ r x) (physicalRoughField x₀ ℓ h ζ x) +
        if side then RoughOutcome.realField R T (a * carriedField S U x₀ r x)
          (targetField x₀ h (a * t * jb) x) else 0 := by
  cases side <;>
    simp only [roughOutcomeFields, codedFields, normalizedRoughOutcome,
      Bool.false_eq_true, if_false, if_true, targetField, codedLikelihood,
      RoughOutcome.likelihood, RoughOutcome.outcome, RoughOutcome.realField] <;> ring

end CausalLowerbound.PartC

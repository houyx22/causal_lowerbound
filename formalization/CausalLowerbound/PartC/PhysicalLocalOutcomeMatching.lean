import CausalLowerbound.PartC.PhysicalLocalSigns
import CausalLowerbound.PartC.PhysicalRoughMoments
import CausalLowerbound.PartC.RemovedOutcomeMatching

/-! Cubic shared-sign matching for separated physical sites. The actual
fourth-moment correction is valid at sites whose effective shift is zero
or the specified physical jitter, as happens off the assignment layer. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative RoughOutcome
variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [LinearOrder V]

theorem physicalRoughCorrection_zero_or_shift (x₀ : d → ℝ) (ℓ h shift jitter jb : ℝ)
    (hℓ : 0 < ℓ) (hh : 0 < h) (x : d → ℝ)
    (hs : coarseBump x₀ h x = 0 ∨ shift = 0 ∨ shift = jitter) :
    (shift * jb * coarseBump x₀ h x ^ 2) * physicalRoughCorrection x₀ ℓ h jitter x =
      shift ^ 3 * jb * independentSigns.expect (fun ζ => physicalRoughField x₀ ℓ h ζ x ^ 4) := by
  rcases hs with hG | hs | hs
  · have hz (ζ : activeBlocks (d := d) ℓ h → Bool) : physicalRoughField x₀ ℓ h ζ x = 0 :=
      physicalRoughField_zero x₀ ℓ h ζ x hG
    simp only [hG, hz, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0),
      mul_zero, zero_mul, FiniteLaw.expect_const]
  · simp only [hs, zero_mul, zero_pow (by decide : 3 ≠ 0)]
  · rw [hs]
    exact physicalRoughCorrection_identity x₀ ℓ h jitter jb hℓ hh x

theorem removed_physical_outcome_coefficient_matching
    {Ω : Type*} [Fintype Ω] (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h) (x : V → d → ℝ)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (R T jb jitter scale offset ψ : V → ℝ)
    (W : Representative.Array d V (activeBlocks (d := d) ℓ h) 3) (u : V × d → ℝ) (τ amp : ℝ)
    (hshift : ∀ i, coarseBump x₀ h (x i) = 0 ∨
      (ψ i * amp) * scale i = 0 ∨ (ψ i * amp) * scale i = jitter i) :
    let B := remove (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) W
    let η := fun i => physicalRoughCorrection x₀ ℓ h (jitter i) (x i)
    independentSigns.expect (fun ζ =>
      outcomeCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ
        (fun i => scale i ^ 2 * coarseBump x₀ h (x i) ^ 2) B u
        (fun i => scale i * physicalRoughField x₀ ℓ h ζ (x i)) ζ
        (retainedOutcomePolynomial Q R T jb η (fun i => physicalRoughField x₀ ℓ h ζ (x i))
          offset ψ (configurationSite u))) =
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) *
        μ.expect (fun ξ => independentSigns.expect (fun ζ =>
          pointValue (torusProjection u) (fun i => scale i * physicalRoughField x₀ ℓ h ζ (x i)) ζ B *
            ((∏ i, (likelihood (R i) (T i) (jb i) (η i)
              (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)) (physicalRoughField x₀ ℓ h ζ (x i)) +
              realField (R i) (T i)
                (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i))
                (((ψ i * amp) * scale i) * jb i * coarseBump x₀ h (x i) ^ 2))) -
              ∏ i, likelihood (R i) (T i) (jb i) (η i)
                (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i))
                (physicalRoughField x₀ ℓ h ζ (x i))))) := by
  exact removed_outcome_coefficient_matching Q hQ hcard μ U
    (fun i => physicalLocalSigns x₀ ℓ h (x i))
    (fun i j hij => physicalLocalSigns_disjoint x₀ ℓ h hℓ (x i) (x j) (hsep i j hij))
    (fun i ζ => physicalRoughField x₀ ℓ h ζ (x i))
    (fun i ζ ζ' hs => physicalRoughField_local_congr x₀ ℓ h (x i) ζ ζ' hs)
    R T jb (fun i => physicalRoughCorrection x₀ ℓ h (jitter i) (x i))
    (fun i => coarseBump x₀ h (x i) ^ 2) scale offset ψ
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).1)
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).2.1)
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).2.2.1) W u τ amp
    (fun i => physicalRoughCorrection_zero_or_shift x₀ ℓ h ((ψ i * amp) * scale i) (jitter i) (jb i)
      hℓ hh (x i) (hshift i))

end CausalLowerbound.PartC

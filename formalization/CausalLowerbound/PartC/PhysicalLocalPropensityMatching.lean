import CausalLowerbound.PartC.PhysicalLocalSigns
import CausalLowerbound.PartC.RemovedPropensityMatching

/-! Shared physical-sign matching for separated sites, after deleting
their actual local symbols. All needed moments and local dependence are
derived from the physical rough field. The deletion costs at most a
fixed number of one-symbol seminorms per observation. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative RoughPropensity
section Bounds
variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]

theorem physicalLocalSigns_union_card (x₀ : d → ℝ) (ℓ h : ℝ) (x : V → d → ℝ) :
    (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))).card ≤
      Fintype.card V * 2 ^ Fintype.card d := by
  calc
    _ ≤ ∑ i : V, (physicalLocalSigns x₀ ℓ h (x i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : V, 2 ^ Fintype.card d := Finset.sum_le_sum (fun i _ => physicalLocalSigns_card x₀ ℓ h (x i))
    _ = _ := by simp

theorem physical_local_removal_bound {D : ℕ} (x₀ : d → ℝ) (ℓ h : ℝ) (x : V → d → ℝ)
    (W : Representative.Array d V (activeBlocks (d := d) ℓ h) D) (C : ℝ) (hC : 0 ≤ C)
    (hsymbol : ∀ j, ‖symbolPart j W‖ ≤ C) :
    ‖W - remove (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) W‖ ≤
      (Fintype.card V : ℝ) * 2 ^ Fintype.card d * C := by
  let S := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))
  calc
    _ ≤ ∑ j ∈ S, ‖symbolPart j W‖ := removal_error S W
    _ ≤ ∑ _j ∈ S, C := Finset.sum_le_sum (fun j _ => hsymbol j)
    _ = (S.card : ℝ) * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast physicalLocalSigns_union_card x₀ ℓ h x) hC

end Bounds
variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [LinearOrder V]

theorem removed_physical_propensity_coefficient_matching
    {Ω : Type*} [Fintype Ω] (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h) (x : V → d → ℝ)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (R T ja scale offset ψ : V → ℝ)
    (W : Representative.Array d V (activeBlocks (d := d) ℓ h) 1) (u : V × d → ℝ) (τ amp : ℝ) :
    let B := remove (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) W
    independentSigns.expect (fun ζ =>
      propensityCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ
        (fun i => scale i ^ 2 * ja i ^ 2 * (coarseBump x₀ h (x i) ^ 2) ^ 2) B u
        (fun i => scale i * physicalRoughField x₀ ℓ h ζ (x i)) ζ
        (retainedPropensityPolynomial Q R T ja (fun i => physicalRoughField x₀ ℓ h ζ (x i))
          offset ψ (configurationSite u))) =
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) *
        μ.expect (fun ξ => independentSigns.expect (fun ζ =>
          pointValue (torusProjection u) (fun i => scale i * physicalRoughField x₀ ℓ h ζ (x i)) ζ B *
            ((∏ i, (likelihood (R i) (T i) (ja i)
              (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i)) (physicalRoughField x₀ ℓ h ζ (x i)) +
              realField (R i) (T i) (ja i) (ja i * (ψ i * amp) * scale i * coarseBump x₀ h (x i) ^ 2)
                (physicalRoughField x₀ ℓ h ζ (x i)))) -
              ∏ i, likelihood (R i) (T i) (ja i)
                (offset i + ψ i * coefficientEvaluation (U ξ) (configurationSite u i))
                (physicalRoughField x₀ ℓ h ζ (x i))))) := by
  exact removed_propensity_coefficient_matching Q hQ hcard μ U
    (fun i => physicalLocalSigns x₀ ℓ h (x i))
    (fun i j hij => physicalLocalSigns_disjoint x₀ ℓ h hℓ (x i) (x j) (hsep i j hij))
    (fun i ζ => physicalRoughField x₀ ℓ h ζ (x i))
    (fun i ζ ζ' hs => physicalRoughField_local_congr x₀ ℓ h (x i) ζ ζ' hs)
    R T ja (fun i => coarseBump x₀ h (x i) ^ 2) scale offset ψ
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).1)
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).2.1) W u τ amp

end CausalLowerbound.PartC

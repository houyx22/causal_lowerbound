import CausalLowerbound.PartC.BlockFunctionalShift
import CausalLowerbound.PartC.GlobalOutcomeShift
import CausalLowerbound.PartC.RetainedObservationSlots
import CausalLowerbound.PartC.TaperedCubicFunctional

/-! Expand the actual coefficient-averaged rough-outcome likelihood as
a full cubic observation polynomial. Taper-zero blocks use the exact
amplitude mask, preserving the unchanged zero-degree carrier weight. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I Ω : Type*} [Fintype d] [DecidableEq d]
  [Fintype I] [DecidableEq I] [Fintype Ω]

theorem mixedOutcomeComponentPolynomial_functional_expansion (Q : ℕ) (hQ : 0 < Q)
    (S : Finset (d → ℤ)) (μ : S → FiniteLaw Ω)
    (U : S → Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h a jb t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (u : S → Fin Q × d → ℝ) (amp : S → ℝ) (τ : ℝ) (slot : S → I → Fin Q)
    (hkeep : ∀ k i, linearPartition (localCoordinate x₀ r k.val (x i)) ≠ 0 →
      configurationSite (u k) (slot k i) = carrierCoordinate (localCoordinate x₀ r k.val (x i)))
    (hχ : ∀ k, amp k ≠ 0 →
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight (u k)) ≠ 0)
    (L : S → MvPolynomial (Fin Q) ℝ →ₗ[ℝ] ℝ) :
    blockPolynomialFunctional (fun k => (L k).comp
      (coefficientShiftAverage (μ k) (U k)
        (fun b v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree b) (u k)) (amp k)))
      (mixedOutcomeComponentPolynomial Q false S x₀ ℓ r h a jb t ζ x y) =
      (FiniteLaw.independent μ).expect (fun ξ => (1 / 4 : ℝ) ^ Fintype.card I *
        blockPolynomialFunctional L (∏ i,
          outcomeTaylorPolynomial (sign (y i).1) (sign (y i).2) 1 jb
            (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
            (a * eval (fun ka => U ka.1 (ξ ka.1) ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
            (physicalRoughField x₀ ℓ h ζ (x i))
            (∑ k : S, C (a * linearPartition (localCoordinate x₀ r k.val (x i)) * amp k) * X (k, slot k i)))) := by
  rw [blockPolynomialFunctional_shift_average_general,
    mixedOutcomeComponentPolynomial_shift_average Q hQ S μ U x₀ ℓ r h a jb t ζ x y u amp τ slot hkeep hχ]
  simp only [map_sum, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  simp only [← map_pow, MvPolynomial.C_mul', map_smul, smul_eq_mul, FiniteLaw.expect]

theorem completed_outcome_tapered_expansion (Q : ℕ) (hQ : 0 < Q)
    (S : Finset (d → ℤ)) (μ : S → FiniteLaw Ω)
    (U : S → Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h a jb t τ : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ghost : ∀ k, G k → d → ℝ) (amp : S → ℝ) (w : S → Degree (Fin Q) 3 → ℝ) :
    let u := fun k : S => completedConfiguration (e k)
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)
    let χ := fun k => graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight (u k))
    let amp' := fun k => if χ k = 0 then 0 else amp k
    blockPolynomialFunctional (fun k => (cubicSiteFunctional (taperedCubicWeight (χ k) (w k))).comp
      (coefficientShiftAverage (μ k) (U k)
        (fun b v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree b) (u k)) (amp k)))
      (mixedOutcomeComponentPolynomial Q false S x₀ ℓ r h a jb t ζ x y) =
      (FiniteLaw.independent μ).expect (fun ξ => (1 / 4 : ℝ) ^ Fintype.card I *
        blockPolynomialFunctional (fun k => cubicSiteFunctional (taperedCubicWeight (χ k) (w k)))
          (∏ i, outcomeTaylorPolynomial (sign (y i).1) (sign (y i).2) 1 jb
            (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
            (a * eval (fun ka => U ka.1 (ξ ka.1) ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
            (physicalRoughField x₀ ℓ h ζ (x i))
            (∑ k : S, C (a * linearPartition (localCoordinate x₀ r k.val (x i)) * amp' k) *
              X (k, retainedObservationSlot Q hQ x₀ r k.val x (e k) i)))) := by
  dsimp only
  let u := fun k : S => completedConfiguration (e k)
    (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)
  let χ := fun k => graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight (u k))
  let amp' := fun k => if χ k = 0 then 0 else amp k
  have hmaps : (fun k : S => (cubicSiteFunctional (taperedCubicWeight (χ k) (w k))).comp
      (coefficientShiftAverage (μ k) (U k)
        (fun b v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree b) (u k)) (amp k))) =
      (fun k : S => (cubicSiteFunctional (taperedCubicWeight (χ k) (w k))).comp
        (coefficientShiftAverage (μ k) (U k)
          (fun b v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree b) (u k)) (amp' k))) := by
    funext k
    apply LinearMap.ext
    intro p
    exact taperedCubicFunctional_mask_amplitude (μ k) (U k) _ (amp k) (χ k) (w k) p
  rw [hmaps]
  apply mixedOutcomeComponentPolynomial_functional_expansion Q hQ S μ U x₀ ℓ r h a jb t ζ x y
    u amp' τ (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k))
  · intro k i hi
    exact retainedObservationSlot_configuration Q hQ x₀ r k.val x (e k) (ghost k) i hi
  · intro k hk hz
    exact hk (if_pos hz)

end CausalLowerbound.PartC

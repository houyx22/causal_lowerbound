import CausalLowerbound.PartC.UntaperedOutcomePatternIntegration
import CausalLowerbound.PartC.OutcomeObservationMatching

/-! The normalized finite cubic expansion is the exact shared-sign
matching expression for the real binary likelihood. The zero pattern
on its right is the same partial carrier used by the physical bridge. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative MvPolynomial
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def outcomeUntaperedObservationValue
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c w N jb shift : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (x : I → d → ℝ) (y : I → Bool × Bool) (smooth : I → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) : ℝ :=
  (1 / 4 : ℝ) ^ Fintype.card I * cubicObservationExpansion
    (fun k f => ghostOutcomePatternIntegral x₀ ℓ r h k.val c w N (B k) (e k)
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
      (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
        (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η f (fun _ => 1))
    (fun i => outcomeTaylorCoefficient (sign (y i).1) (sign (y i).2) 1 jb
      (physicalRoughCorrection x₀ ℓ h shift (x i)) (smooth i) (physicalRoughField x₀ ℓ h ζ (x i)))
    (fun i k => linearPartition (localCoordinate x₀ r k.val (x i)))
    (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) shift

private theorem outcome_constant_functional {A : Type*}
    (L : MvPolynomial A ℝ →ₗ[ℝ] ℝ) (c : ℝ) (p : MvPolynomial A ℝ) :
    L (C c * p) = c * L p := by
  rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]

theorem outcomeObservationPolynomial_untapered_integral
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (U : S → CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h c w N a jb t : ℝ) (hc : 0 < c)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) :
    (∫ ghost : ∀ k, G k → d → ℝ, blockPolynomialFunctional
      (fun k => partialPhysicalOutcomeFunctional x₀ ℓ r h k.val c w N (B k) (e k)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
        (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
          (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η (ghost k))
      (outcomeObservationPolynomial Q hQ S U x₀ ℓ r h N a jb t ζ x y G e)
      ∂Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))) =
      outcomeUntaperedObservationValue Q hQ S x₀ ℓ r h c w N jb (a * t) B x y
        (fun i => a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i))) G e ζ η := by
  simp only [outcomeObservationPolynomial, outcome_constant_functional, integral_const_mul]
  unfold outcomeUntaperedObservationValue
  apply congrArg (fun v : ℝ => (1 / 4 : ℝ) ^ Fintype.card I * v)
  have hamp (z : ℝ) : (a * z) * (t * N) = ((a * t) * N) * z := by ring
  simp_rw [outcomeTaylorPolynomial_eq_sum, hamp]
  exact outcome_untapered_observation_integral Q x₀ ℓ r h (fun k : S => k.val) c w N (a * t) hc
    (fun k : S => {i // x i ∈ carrierBox x₀ r k.val}) G B e
    (fun k i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
    (fun k i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
      (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η
    (fun i => outcomeTaylorCoefficient (sign (y i).1) (sign (y i).2) 1 jb
      (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
      (a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
      (physicalRoughField x₀ ℓ h ζ (x i)))
    (fun i k => linearPartition (localCoordinate x₀ r k.val (x i)))
    (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k))

theorem physical_outcome_untapered_pattern_matching
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (U : S → CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h c w N a jb t : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hc : 0 < c)
    (hw : 0 < w) (hw1 : w ≤ 1) (hN : N ≠ 0)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      outcomeUntaperedObservationValue Q hQ S x₀ ℓ r h c w N jb (a * t) B x y
        (fun i => a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i))) G e ζ η) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      (∏ k, ghostOutcomePatternIntegral x₀ ℓ r h k.val c w N (B k) (e k)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
        (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
          (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η 0 (fun _ => 1)) *
        eval (fun ka => U ka.1 ka.2) (mixedOutcomeComponentPolynomial Q true S x₀ ℓ r h a jb t ζ x y)) ζ) := by
  have he := physical_outcome_observation_ghost_matching Q hQ S U x₀ ℓ r h c w N a jb t
    hℓ hr hh hc hw hw1 hN hm x y hsep hcover htr B G e
  dsimp only at he
  simp only [outcomeObservationPolynomial_untapered_integral Q hQ S U x₀ ℓ r h c w N a jb t hc B x y G e] at he
  simpa only [ghostOutcomePatternIntegral_zero] using he

end CausalLowerbound.PartC

import CausalLowerbound.PartC.UntaperedOutcomeObservationMatching
import CausalLowerbound.PartC.CubicObservationBaseline

/-! Cancel the unique zero-degree observation choice from the exact
cubic matching identity. The remaining finite sum is precisely the
real likelihood increment, with the same partial carrier on both sides. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def outcomeUntaperedPositiveValue
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c w N jb shift : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (x : I → d → ℝ) (y : I → Bool × Bool) (smooth : I → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) : ℝ :=
  (1 / 4 : ℝ) ^ Fintype.card I * ∑ s ∈ Finset.univ.erase cubicZeroChoice,
    cubicObservationTerm
      (fun k f => ghostOutcomePatternIntegral x₀ ℓ r h k.val c w N (B k) (e k)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
        (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
          (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η f (fun _ => 1))
      (fun i => outcomeTaylorCoefficient (sign (y i).1) (sign (y i).2) 1 jb
        (physicalRoughCorrection x₀ ℓ h shift (x i)) (smooth i) (physicalRoughField x₀ ℓ h ζ (x i)))
      (fun i k => linearPartition (localCoordinate x₀ r k.val (x i)))
      (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) shift s

private theorem cubic_baseline_difference (c b w p : ℝ) :
    c * (b * w + p) - w * (c * b) = c * p := by ring

theorem outcomeUntaperedPositiveValue_eq_sub
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (U : S → CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h c w N a jb t : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) :
    outcomeUntaperedPositiveValue Q hQ S x₀ ℓ r h c w N jb (a * t) B x y
      (fun i => a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i))) G e ζ η =
      outcomeUntaperedObservationValue Q hQ S x₀ ℓ r h c w N jb (a * t) B x y
        (fun i => a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i))) G e ζ η -
      (∏ k, ghostOutcomePatternIntegral x₀ ℓ r h k.val c w N (B k) (e k)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
        (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
          (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η 0 (fun _ => 1)) *
        eval (fun ka => U ka.1 ka.2) (mixedOutcomeComponentPolynomial Q false S x₀ ℓ r h a jb t ζ x y) := by
  let W := fun (k : S) (f : Degree (Fin Q) 3) =>
    ghostOutcomePatternIntegral x₀ ℓ r h k.val c w N (B k) (e k)
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
      (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
        (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η f (fun _ => 1)
  let b := fun i => outcomeTaylorCoefficient (sign (y i).1) (sign (y i).2) 1 jb
    (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
    (a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
    (physicalRoughField x₀ ℓ h ζ (x i))
  let δ := fun (i : I) (k : S) => linearPartition (localCoordinate x₀ r k.val (x i))
  let slot := fun k : S => retainedObservationSlot Q hQ x₀ r k.val x (e k)
  have hzero : (1 / 4 : ℝ) ^ Fintype.card I * (∏ i, b i 0) =
      eval (fun ka => U ka.1 ka.2) (mixedOutcomeComponentPolynomial Q false S x₀ ℓ r h a jb t ζ x y) := by
    rw [mixedOutcomeComponentPolynomial_eval_likelihood]
    simp only [b, outcomeTaylorCoefficient, if_pos rfl, if_true, Bool.false_eq_true, if_false, add_zero]
  change (1 / 4 : ℝ) ^ Fintype.card I *
      (∑ s ∈ Finset.univ.erase cubicZeroChoice, cubicObservationTerm W b δ slot (a * t) s) =
    (1 / 4 : ℝ) ^ Fintype.card I * cubicObservationExpansion W b δ slot (a * t) -
      (∏ k, W k 0) * eval (fun ka => U ka.1 ka.2)
        (mixedOutcomeComponentPolynomial Q false S x₀ ℓ r h a jb t ζ x y)
  rw [cubicObservationExpansion_baseline, ← hzero]
  exact (cubic_baseline_difference _ _ _ _).symm

theorem physical_outcome_untapered_increment_matching
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
      outcomeUntaperedPositiveValue Q hQ S x₀ ℓ r h c w N jb (a * t) B x y
        (fun i => a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i))) G e ζ η) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      (∏ k, ghostOutcomePatternIntegral x₀ ℓ r h k.val c w N (B k) (e k)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
        (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
          (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η 0 (fun _ => 1)) *
        (eval (fun ka => U ka.1 ka.2) (mixedOutcomeComponentPolynomial Q true S x₀ ℓ r h a jb t ζ x y) -
          eval (fun ka => U ka.1 ka.2) (mixedOutcomeComponentPolynomial Q false S x₀ ℓ r h a jb t ζ x y))) ζ) := by
  let T := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))
  let base := fun (ζ η : activeBlocks (d := d) ℓ h → Bool) =>
    ∏ k, ghostOutcomePatternIntegral x₀ ℓ r h k.val c w N (B k) (e k)
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
      (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
        (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η 0 (fun _ => 1)
  let cells := fun side ζ => eval (fun ka => U ka.1 ka.2)
    (mixedOutcomeComponentPolynomial Q side S x₀ ℓ r h a jb t ζ x y)
  have he := physical_outcome_untapered_pattern_matching Q hQ S U x₀ ℓ r h c w N a jb t
    hℓ hr hh hc hw hw1 hN hm x y hsep hcover htr B G e
  simp_rw [outcomeUntaperedPositiveValue_eq_sub, mul_sub, Walsh.resampleAverage, FiniteLaw.expect_sub]
  exact congrArg (fun z : ℝ => z - independentSigns.expect
    (fun ζ => Walsh.resampleAverage T (fun η => base ζ η * cells false ζ) ζ)) he

end CausalLowerbound.PartC

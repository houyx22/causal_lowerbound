import CausalLowerbound.PartC.OutcomeGhostIntegration
import CausalLowerbound.PartC.GlobalOutcomeShift

/-! The ghost-integrated cubic identity has the actual normalized
binary observation likelihood on its real side. The coefficients are
arbitrary fixed values, so subsequent averaging uses the same identity. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative MvPolynomial RoughOutcome
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem mixedOutcomeComponentPolynomial_eval_likelihood (Q : ℕ) (side : Bool)
    (S : Finset (d → ℤ)) (U : S → CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : I → d → ℝ) (y : I → Bool × Bool) :
    eval (fun ka => U ka.1 ka.2) (mixedOutcomeComponentPolynomial Q side S x₀ ℓ r h a jb t ζ x y) =
      (1 / 4 : ℝ) ^ Fintype.card I * ∏ i,
        (likelihood (sign (y i).1) (sign (y i).2) jb (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
          (a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
          (physicalRoughField x₀ ℓ h ζ (x i)) +
        if side then realField (sign (y i).1) (sign (y i).2)
          (a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
          (targetField x₀ h (a * t * jb) (x i)) else 0) := by
  simp only [mixedOutcomeComponentPolynomial, mixedOutcomeCellPolynomial, map_prod, map_mul,
    map_pow, eval_C, outcomeSitePolynomial_eval, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

def outcomeObservationPolynomial (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ))
    (U : S → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h N a jb t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) : MvPolynomial (S × Fin Q) ℝ :=
  C ((1 / 4 : ℝ) ^ Fintype.card I) *
    ∏ i, outcomeTaylorPolynomial (sign (y i).1) (sign (y i).2) 1 jb
      (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
      (a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
      (physicalRoughField x₀ ℓ h ζ (x i))
      (∑ k : S, C ((a * linearPartition (localCoordinate x₀ r k.val (x i))) * (t * N)) *
        X (k, retainedObservationSlot Q hQ x₀ r k.val x (e k) i))

private theorem outcome_functional_normalization {A : Type*}
    (L : MvPolynomial A ℝ →ₗ[ℝ] ℝ) (c : ℝ) (p : MvPolynomial A ℝ) :
    L (C c * p) = c * L p := by
  rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]

set_option maxHeartbeats 400000 in
theorem physical_outcome_observation_ghost_matching
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
    let u₀ := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
      carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
    let z₀ := fun (ζ : activeBlocks (d := d) ℓ h → Bool) (k : S)
      (i : {i // x i ∈ carrierBox x₀ r k.val}) => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (u₀ k i)
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      ∫ ghost : ∀ k, G k → d → ℝ, blockPolynomialFunctional
        (fun k => partialPhysicalOutcomeFunctional x₀ ℓ r h k.val c w N (B k) (e k) (u₀ k) (z₀ ζ k) η (ghost k))
        (outcomeObservationPolynomial Q hQ S U x₀ ℓ r h N a jb t ζ x y G e)
          ∂Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      (∏ k, ∫ ghost : G k → d → ℝ,
        partialPhysicalCarrierValue x₀ ℓ r h k.val c w N (B k) (e k) (u₀ k) (z₀ ζ k) η ghost
          ∂Measure.pi (fun _ : G k => cubeMeasure d)) *
        eval (fun ka => U ka.1 ka.2) (mixedOutcomeComponentPolynomial Q true S x₀ ℓ r h a jb t ζ x y)) ζ) := by
  have he := physical_completed_outcome_ghost_matching Q hQ S x₀ ℓ r h c w N a jb t
    hℓ hr hh hc hw hw1 hN hm x (fun i => sign (y i).1) (fun i => sign (y i).2)
    (fun i => a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
    hsep hcover htr B G e
  have hg (ζ : activeBlocks (d := d) ℓ h → Bool) (q : ℝ) :
      q * eval (fun ka => U ka.1 ka.2) (mixedOutcomeComponentPolynomial Q true S x₀ ℓ r h a jb t ζ x y) =
        (1 / 4 : ℝ) ^ Fintype.card I * (q * ∏ i,
          (likelihood (sign (y i).1) (sign (y i).2) jb (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
            (a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
            (physicalRoughField x₀ ℓ h ζ (x i)) +
          realField (sign (y i).1) (sign (y i).2)
            (a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
            (targetField x₀ h (a * t * jb) (x i)))) := by
    rw [mixedOutcomeComponentPolynomial_eval_likelihood]
    simp only [if_true]
    exact mul_left_comm _ _ _
  dsimp only at he ⊢
  simp only [outcomeObservationPolynomial, outcome_functional_normalization,
    integral_const_mul, hg, Walsh.resampleAverage, FiniteLaw.expect_mul]
  exact congrArg (fun z : ℝ => (1 / 4 : ℝ) ^ Fintype.card I * z) he

end CausalLowerbound.PartC

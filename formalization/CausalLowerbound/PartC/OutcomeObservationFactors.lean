import CausalLowerbound.PartC.CubicObservationChoiceInstances
import CausalLowerbound.PartC.OutcomeObservationTaperRemoval
import CausalLowerbound.PartC.OutcomeObservationIncrementMatching
import CausalLowerbound.PartC.IntegratedOutcomeObservation

/-! A common finite-choice interface for the actual tapered observation,
the untapered matching expression, and their identical zero pattern. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def outcomeObservationPatternWeight
    (taper : Bool) (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c w N τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (k : S) (f : Degree (Fin Q) 3) : ℝ :=
  if taper then
    physicalGhostOutcomePatternWeight Q x₀ ℓ r h k.val c w N τ (B k) (e k)
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) ζ η f
  else
    ghostOutcomePatternIntegral x₀ ℓ r h k.val c w N (B k) (e k)
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
      (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
        (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η f (fun _ => 1)

def outcomeObservationPatternProduct
    (taper : Bool) (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (s : I → CubicObservationChoice S) (ζ η : activeBlocks (d := d) ℓ h → Bool) : ℝ :=
  cubicObservationPatternProduct (outcomeObservationPatternWeight taper Q S x₀ ℓ r h c w N τ B x G e ζ η)
    (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) s

def outcomeObservationValue
    (taper : Bool) (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N jb shift τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (x : I → d → ℝ) (y : I → Bool × Bool) (smooth : I → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) : ℝ :=
  (1 / 4 : ℝ) ^ Fintype.card I * cubicObservationExpansion
    (outcomeObservationPatternWeight taper Q S x₀ ℓ r h c w N τ B x G e ζ η)
    (fun i => outcomeTaylorCoefficient (sign (y i).1) (sign (y i).2) 1 jb
      (physicalRoughCorrection x₀ ℓ h shift (x i)) (smooth i) (physicalRoughField x₀ ℓ h ζ (x i)))
    (fun i k => linearPartition (localCoordinate x₀ r k.val (x i)))
    (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) shift

theorem outcomeObservationPatternProduct_valid
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c w N τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (s : I → CubicObservationChoice S)
    (hs : ∀ v, siteOccurrenceExponent
      (cubicObservationChoiceSlot (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) s) v ≤ 3)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) :
    outcomeObservationPatternProduct true Q hQ S x₀ ℓ r h c w N τ B x G e s ζ η =
      outcomeObservationChoiceGhostProduct Q hQ S x₀ ℓ r h c w N τ B x G e s hs ζ η ∧
    outcomeObservationPatternProduct false Q hQ S x₀ ℓ r h c w N τ B x G e s ζ η =
      outcomeObservationChoiceUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N B x G e s hs ζ η := by
  constructor <;>
    dsimp only [outcomeObservationChoiceGhostProduct, outcomeObservationChoiceUntaperedGhostProduct] <;>
    simp only [outcomeObservationPatternProduct, cubicObservationPatternProduct, dif_pos hs,
      outcomeObservationPatternWeight, if_pos rfl, if_true, Bool.false_eq_true, if_false]

theorem outcomeObservationPatternProduct_invalid
    (taper : Bool) (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (s : I → CubicObservationChoice S)
    (hs : ¬ ∀ v, siteOccurrenceExponent
      (cubicObservationChoiceSlot (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) s) v ≤ 3)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) :
    outcomeObservationPatternProduct taper Q hQ S x₀ ℓ r h c w N τ B x G e s ζ η = 0 := by
  simp only [outcomeObservationPatternProduct, cubicObservationPatternProduct, dif_neg hs]

theorem outcomeObservationPatternWeight_zero
    (taper : Bool) (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c w N τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (k : S) :
    outcomeObservationPatternWeight taper Q S x₀ ℓ r h c w N τ B x G e ζ η k 0 =
      outcomeObservationPatternWeight false Q S x₀ ℓ r h c w N τ B x G e ζ η k 0 := by
  cases taper
  · rfl
  · have he : selectedOutcomeGhostTaper Q (e k) τ
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (0 : Degree (Fin Q) 3) =
          (fun _ : G k → d → ℝ => (1 : ℝ)) := by
      funext g
      simp only [selectedOutcomeGhostTaper, if_pos rfl, if_true]
    simp only [outcomeObservationPatternWeight, if_pos rfl, if_true,
      Bool.false_eq_true, if_false, physicalGhostOutcomePatternWeight, he]

theorem outcomeUntaperedPositiveValue_factor
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c w N jb shift τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (x : I → d → ℝ) (y : I → Bool × Bool) (smooth : I → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) :
    outcomeUntaperedPositiveValue Q hQ S x₀ ℓ r h c w N jb shift B x y smooth G e ζ η =
      ∑ s ∈ Finset.univ.erase cubicZeroChoice,
        outcomeObservationChoiceCoefficient S x₀ ℓ r h jb shift x y smooth s ζ *
          outcomeObservationPatternProduct false Q hQ S x₀ ℓ r h c w N τ B x G e s ζ η := by
  have he := cubicObservationPositive_factor ((1 / 4 : ℝ) ^ Fintype.card I)
    (outcomeObservationPatternWeight false Q S x₀ ℓ r h c w N τ B x G e ζ η)
    (fun i => outcomeTaylorCoefficient (sign (y i).1) (sign (y i).2) 1 jb
      (physicalRoughCorrection x₀ ℓ h shift (x i)) (smooth i) (physicalRoughField x₀ ℓ h ζ (x i)))
    (fun i k => linearPartition (localCoordinate x₀ r k.val (x i)))
    (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) shift
  have hfin : finOrderedDecEq Q = instDecidableEqFin Q := Subsingleton.elim _ _
  unfold outcomeUntaperedPositiveValue outcomeObservationPatternProduct
    outcomeObservationChoiceCoefficient
  unfold cubicObservationCoefficient at he
  unfold outcomeObservationPatternWeight at he ⊢
  simp only [Bool.false_eq_true, if_false] at he ⊢
  rw [hfin] at he
  rw [hfin]
  exact he

theorem outcomeObservationValue_baseline
    (taper : Bool) (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ))
    (U : S → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h c w N a jb t τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) :
    let smooth := fun i => a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i))
    outcomeObservationValue taper Q hQ S x₀ ℓ r h c w N jb (a * t) τ B x y smooth G e ζ η =
      (∑ s ∈ Finset.univ.erase cubicZeroChoice,
        outcomeObservationChoiceCoefficient S x₀ ℓ r h jb (a * t) x y smooth s ζ *
          outcomeObservationPatternProduct taper Q hQ S x₀ ℓ r h c w N τ B x G e s ζ η) +
      (∏ k, outcomeObservationPatternWeight false Q S x₀ ℓ r h c w N τ B x G e ζ η k 0) *
        eval (fun ka => U ka.1 ka.2) (mixedOutcomeComponentPolynomial Q false S x₀ ℓ r h a jb t ζ x y) := by
  dsimp only
  let b := fun i => outcomeTaylorCoefficient (sign (y i).1) (sign (y i).2) 1 jb
    (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
    (a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
    (physicalRoughField x₀ ℓ h ζ (x i))
  have hzero : (1 / 4 : ℝ) ^ Fintype.card I * (∏ i, b i 0) =
      eval (fun ka => U ka.1 ka.2) (mixedOutcomeComponentPolynomial Q false S x₀ ℓ r h a jb t ζ x y) := by
    rw [mixedOutcomeComponentPolynomial_eval_likelihood]
    simp only [b, outcomeTaylorCoefficient, if_pos rfl, if_true, Bool.false_eq_true, if_false, add_zero]
  have he := cubicObservationExpansion_factor_baseline ((1 / 4 : ℝ) ^ Fintype.card I)
    (outcomeObservationPatternWeight taper Q S x₀ ℓ r h c w N τ B x G e ζ η) b
    (fun i k => linearPartition (localCoordinate x₀ r k.val (x i)))
    (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) (a * t)
  rw [hzero] at he
  simp_rw [outcomeObservationPatternWeight_zero taper] at he
  simpa only [outcomeObservationValue, outcomeObservationChoiceCoefficient,
    outcomeObservationPatternProduct, cubicObservationCoefficient, b] using he

end CausalLowerbound.PartC

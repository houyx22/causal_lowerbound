import CausalLowerbound.PartC.RawCarrierConditional
import CausalLowerbound.PartC.RawOutcomeCrudeComparison

/-! Actual conditional experiments from the constructed cubic outcome carrier.
Both the unrestricted comparison and the separated-interior comparison are
converted to squared Hellinger bounds using their common design marginal. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]
  {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}

def outcomeWitnessConditional
    (Q : ℕ) (ρ : ℝ) (side : Bool) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t τ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (R : ∀ k : S, OutcomeMomentWitness Q ρ x₀ ℓ r h k.val c w N θ t τ)
    (hlegal : ∀ ζ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (roughOutcomeFields side S (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S ξ k))
        x₀ ℓ r h a jb t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (x : I → d → ℝ) : FiniteLaw (I → Bool × Bool) :=
  rawCarrierConditional
    (fun z : (S → ℕ) × (activeBlocks (d := d) ℓ h → Bool) =>
      physicalCarrierProfile (ι := Fin Q) (D := 3) x₀ ℓ r h c w N N₀ θ
        hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S z.1) z.2)
    hθ hθ1 S x₀ r (fun k => (R k).law)
    (fun k ζ n => if side then paperCoefficientLaw Q else (R k).kernel ζ n)
    (fun z => roughOutcomeFields side S
      (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S z.2 k)) x₀ ℓ r h a jb t z.1.2)
    (fun z => hlegal z.1.2 z.2) hκ x

theorem outcome_witness_conditional_crude_hellinger
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t τ C₀ δ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1) (hshift : 0 ≤ a * t) (hsjb : a * t ≤ jb)
    (hcarr : ∀ k : S, HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ t τ C₀ δ)
    (R : ∀ k : S, OutcomeMomentWitness Q ρ x₀ ℓ r h k.val c w N θ t τ)
    (hlegal : ∀ side ζ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (roughOutcomeFields side S (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S ξ k))
        x₀ ℓ r h a jb t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 < κ) (x : I → d → ℝ) (hcard : Fintype.card I ≤ Q)
    (G : S → Type) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (hsmooth : ∀ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    let P := fun side => outcomeWitnessConditional Q ρ side S x₀ ℓ r h c w N N₀ θ a jb t τ
      hℓ hr hc hN₀ hN hθ hθ1 hm hrough R (hlegal side) hκ.le x
    (P false).hellingerSq (P true) ≤
      (Fintype.card (I → Bool × Bool) : ℝ) *
        (outcomeCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |a * t * jb| /
          ((1 - θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I) ^ 2 / (κ ^ 2) ^ Fintype.card I := by
  let F := fun z : (S → ℕ) × (activeBlocks (d := d) ℓ h → Bool) =>
    physicalCarrierProfile (ι := Fin Q) (D := 3) x₀ ℓ r h c w N N₀ θ
      hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S z.1) z.2
  let kernel := fun (side : Bool) (k : S) ζ n => if side then paperCoefficientLaw Q else (R k).kernel ζ n
  let fields := fun (side : Bool) (z : ((S → ℕ) × (activeBlocks (d := d) ℓ h → Bool)) ×
      (S → MomentGrid (CoefficientExponent d Q) (4 * Q))) =>
    roughOutcomeFields side S (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S z.2 k))
      x₀ ℓ r h a jb t z.1.2
  have herr (y : I → Bool × Bool) :
      |(signBlockPrior (fun k => (R k).law) (kernel false)).expect (fun z => ∏ i,
          (F z.1).product S x₀ r (x i) * nuisanceCellMass (fields false z) (x i) (y i)) -
        (signBlockPrior (fun k => (R k).law) (kernel true)).expect (fun z => ∏ i,
          (F z.1).product S x₀ r (x i) * nuisanceCellMass (fields true z) (x i) (y i))| ≤
      outcomeCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |a * t * jb| :=
    physical_outcome_raw_crude_bound Q hQ ρ S x₀ ℓ r h c w N N₀ θ a jb t τ C₀ δ
      hℓ hr hc hN₀ hN hθ hm hrough hjb hsmall hshift hsjb hcarr R x y hcard G e hsmooth
  exact rawCarrierConditional_hellinger_of_raw_bound F hθ hθ1 S x₀ r (fun k => (R k).law)
    kernel fields (fun side z => hlegal side z.1.2 z.2) hκ x _ herr

theorem outcome_witness_conditional_good_hellinger
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t τ C₀ δ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hw : 0 < w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (hmb : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1) (hshift : 0 ≤ a * t) (hsjb : a * t ≤ jb)
    (hcarr : ∀ k : S, HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ t τ C₀ δ)
    (R : ∀ k : S, OutcomeMomentWitness Q ρ x₀ ℓ r h k.val c w N θ t τ)
    (hlegal : ∀ side ζ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (roughOutcomeFields side S (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S ξ k))
        x₀ ℓ r h a jb t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 < κ) (x : I → d → ℝ) (hcard : Fintype.card I ≤ Q)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (G : S → Type) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (hsmooth : ∀ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    let P := fun side => outcomeWitnessConditional Q ρ side S x₀ ℓ r h c w N N₀ θ a jb t τ
      hℓ hr hc hN₀ hN hθ hθ1 hmb hrough R (hlegal side) hκ.le x
    let E := (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (fun σ =>
      outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ
        (fun k => (R k).representative) x G (fun k => (e k).trans (σ k).symm))
    (P false).hellingerSq (P true) ≤ (Fintype.card (I → Bool × Bool) : ℝ) *
      (E / ((1 - θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I) ^ 2 / (κ ^ 2) ^ Fintype.card I := by
  let F := fun z : (S → ℕ) × (activeBlocks (d := d) ℓ h → Bool) =>
    physicalCarrierProfile (ι := Fin Q) (D := 3) x₀ ℓ r h c w N N₀ θ
      hℓ hr hc hN₀ hN hmb hrough hθ (extendBlockSample S z.1) z.2
  let kernel := fun (side : Bool) (k : S) ζ n => if side then paperCoefficientLaw Q else (R k).kernel ζ n
  let fields := fun (side : Bool) (z : ((S → ℕ) × (activeBlocks (d := d) ℓ h → Bool)) ×
      (S → MomentGrid (CoefficientExponent d Q) (4 * Q))) =>
    roughOutcomeFields side S (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S z.2 k))
      x₀ ℓ r h a jb t z.1.2
  let E := (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (fun σ =>
    outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ
      (fun k => (R k).representative) x G (fun k => (e k).trans (σ k).symm))
  have herr (y : I → Bool × Bool) :
      |(signBlockPrior (fun k => (R k).law) (kernel false)).expect (fun z => ∏ i,
          (F z.1).product S x₀ r (x i) * nuisanceCellMass (fields false z) (x i) (y i)) -
        (signBlockPrior (fun k => (R k).law) (kernel true)).expect (fun z => ∏ i,
          (F z.1).product S x₀ r (x i) * nuisanceCellMass (fields true z) (x i) (y i))| ≤ E :=
    physical_outcome_raw_comparison_bound Q hQ ρ S x₀ ℓ r h c w N N₀ θ a jb t τ C₀ δ
      hℓ hr hh hc hw hw1 hN₀ hN hθ hmb hm hrough hjb hsmall hshift hsjb hcarr R x y hcard
      hsep hcover htr G e hsmooth
  exact rawCarrierConditional_hellinger_of_raw_bound F hθ hθ1 S x₀ r (fun k => (R k).law)
    kernel fields (fun side z => hlegal side z.1.2 z.2) hκ x E herr

end CausalLowerbound.PartC


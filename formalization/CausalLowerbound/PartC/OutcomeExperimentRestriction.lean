import CausalLowerbound.PartC.RawConditionalRestriction
import CausalLowerbound.PartC.OutcomeBlockRestriction
import CausalLowerbound.PartC.OutcomeConditionalBounds
import CausalLowerbound.PartC.SupportedAssignmentGeometry

/-! The actual outcome witness experiment is unchanged after removing
blocks not incident to the observations. The law and coefficient kernel
on retained blocks are taken from the original witness. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]
  {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}

theorem outcomeWitnessConditional_restrict
    (Q : ℕ) (ρ : ℝ) (side : Bool) (S T : Finset (d → ℤ)) (hTS : T ⊆ S) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t τ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (R : ∀ k : S, OutcomeMomentWitness Q ρ x₀ ℓ r h k.val c w N θ t τ)
    (hlegal : ∀ ζ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (roughOutcomeFields side S (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S ξ k))
        x₀ ℓ r h a jb t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hlegal' : ∀ ζ (ξ : T → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (roughOutcomeFields side T (fun k => paperCoefficientAtoms Q ρ (extendBlockSample T ξ k))
        x₀ ℓ r h a jb t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (x : I → d → ℝ)
    (hcover : ∀ i k, k ∈ S → x i ∈ carrierBox x₀ r k → k ∈ T) :
    outcomeWitnessConditional Q ρ side S x₀ ℓ r h c w N N₀ θ a jb t τ
      hℓ hr hc hN₀ hN hθ hθ1 hm hrough R hlegal hκ x =
    outcomeWitnessConditional Q ρ side T x₀ ℓ r h c w N N₀ θ a jb t τ
      hℓ hr hc hN₀ hN hθ hθ1 hm hrough
      (fun k : T => R ⟨k.val, hTS k.property⟩) hlegal' hκ x := by
  unfold outcomeWitnessConditional
  refine rawCarrierConditional_finset_restrict S T hTS x₀ r _ _ hθ hθ1 _ _ _ _ _ _ hκ x ?_ ?_
  · intro labels ζ i
    exact physicalCarrierProfile_product_restrict x₀ ℓ r h c w N N₀ θ
      hℓ hr hc hN₀ hN hm hrough hθ S T hTS labels ζ (x i) (hcover i)
  · intro labels ζ ξ i y
    exact roughOutcome_cell_restrict_sample Q side S T hTS (paperCoefficientAtoms Q ρ) ξ
      x₀ ℓ r h a jb t hr ζ (x i) y (hcover i)

theorem outcomeWitnessConditional_configurationBlocks
    (Q : ℕ) (ρ : ℝ) (side : Bool) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t τ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (R : ∀ k : S, OutcomeMomentWitness Q ρ x₀ ℓ r h k.val c w N θ t τ)
    (hκ : 0 ≤ κ) (x : I → d → ℝ)
    (hlegal : ∀ ζ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (roughOutcomeFields side S (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S ξ k))
        x₀ ℓ r h a jb t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hlegal' : ∀ ζ (ξ : configurationBlocks S x₀ r x → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (roughOutcomeFields side (configurationBlocks S x₀ r x)
        (fun k => paperCoefficientAtoms Q ρ (extendBlockSample (configurationBlocks S x₀ r x) ξ k))
        x₀ ℓ r h a jb t ζ).Legal α β γ Lπ L₀ Lτ κ) :
    outcomeWitnessConditional Q ρ side S x₀ ℓ r h c w N N₀ θ a jb t τ
      hℓ hr hc hN₀ hN hθ hθ1 hm hrough R hlegal hκ x =
    outcomeWitnessConditional Q ρ side (configurationBlocks S x₀ r x) x₀ ℓ r h c w N N₀ θ a jb t τ
      hℓ hr hc hN₀ hN hθ hθ1 hm hrough
      (fun k => R ⟨k.val, configurationBlocks_subset S x₀ r x k.property⟩) hlegal' hκ x := by
  apply outcomeWitnessConditional_restrict Q ρ side S (configurationBlocks S x₀ r x)
    (configurationBlocks_subset S x₀ r x) x₀ ℓ r h c w N N₀ θ a jb t τ
    hℓ hr hc hN₀ hN hθ hθ1 hm hrough R hlegal hlegal' hκ x
  intro i k hk hi
  exact (mem_configurationBlocks S x₀ r x k).mpr ⟨hk, i, hi⟩

end CausalLowerbound.PartC


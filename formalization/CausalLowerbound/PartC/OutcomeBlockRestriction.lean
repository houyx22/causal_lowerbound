import CausalLowerbound.PartC.RawOutcomeComparison
import CausalLowerbound.PartC.PhysicalBlockRestriction

/-! Removing blocks not incident to the observations preserves the
actual rough-outcome cells and the cubic design-weighted likelihood. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I Ω : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]
  [Fintype Ω] [Inhabited Ω]

theorem roughOutcome_cell_restrict_sample (Q : ℕ) (side : Bool)
    (S T : Finset (d → ℤ)) (hTS : T ⊆ S) (atoms : Ω → CoefficientExponent d Q → ℝ)
    (ξ : S → Ω) (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (hr : 0 < r)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ) (y : Bool × Bool)
    (hcover : ∀ k ∈ S, x ∈ carrierBox x₀ r k → k ∈ T) :
    nuisanceCellMass (roughOutcomeFields side S (fun k => atoms (extendBlockSample S ξ k))
      x₀ ℓ r h a jb t ζ) x y =
    nuisanceCellMass (roughOutcomeFields side T
      (fun k => atoms (extendBlockSample T (fun k : T => ξ ⟨k.val, hTS k.property⟩) k))
      x₀ ℓ r h a jb t ζ) x y := by
  unfold nuisanceCellMass
  rw [roughOutcomeFields_likelihood, roughOutcomeFields_likelihood,
    carriedField_restrict_sample Q S T hTS atoms ξ x₀ r hr x hcover]

theorem physicalOutcomeRawLikelihood_restrict
    (Q : ℕ) (ρ : ℝ) (side : Bool) (S T : Finset (d → ℤ)) (hTS : T ⊆ S) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀) (hθ : 0 ≤ θ)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hcover : ∀ i k, k ∈ S → x i ∈ carrierBox x₀ r k → k ∈ T)
    (v : ((S → ℕ) × (activeBlocks (d := d) ℓ h → Bool)) ×
      (S → MomentGrid (CoefficientExponent d Q) (4 * Q))) :
    physicalOutcomeRawLikelihood Q ρ side S x₀ ℓ r h c w N N₀ θ a jb t
      hℓ hr hc hN₀ hN hm hrough hθ x y v =
    physicalOutcomeRawLikelihood Q ρ side T x₀ ℓ r h c w N N₀ θ a jb t
      hℓ hr hc hN₀ hN hm hrough hθ x y
      ((fun k : T => v.1.1 ⟨k.val, hTS k.property⟩, v.1.2), fun k : T => v.2 ⟨k.val, hTS k.property⟩) := by
  unfold physicalOutcomeRawLikelihood
  apply Finset.prod_congr rfl
  intro i _
  rw [physicalCarrierProfile_product_restrict x₀ ℓ r h c w N N₀ θ
    hℓ hr hc hN₀ hN hm hrough hθ S T hTS v.1.1 v.1.2 (x i) (hcover i)]
  rw [roughOutcome_cell_restrict_sample Q side S T hTS (paperCoefficientAtoms Q ρ) v.2
    x₀ ℓ r h a jb t hr v.1.2 (x i) (y i) (hcover i)]

end CausalLowerbound.PartC

import CausalLowerbound.PartC.RawConditionalFactorization
import CausalLowerbound.PartC.PropensityExperimentRestriction

/-! Hellinger subadditivity for the actual propensity witness experiments.
The enlarged graph accounts for every shared sign read by an observation,
carrier density, or coefficient kernel. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt incidenceComponentFintype
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]
  {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}

theorem propensity_witness_component_hellinger
    (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ ja b t τ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (R : ∀ k : S, PropensityMomentWitness Q ρ x₀ ℓ r h k.val c w N θ ja t τ)
    (hlegal : ∀ side ζ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (roughPropensityFields side S (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S ξ k))
        x₀ ℓ r h ja b t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (x : I → d → ℝ) :
    let inc := physicalSharedIncidence S x₀ ℓ r h x
    let P := fun side => propensityWitnessConditional Q ρ side S x₀ ℓ r h c w N N₀ θ ja b t τ
      hℓ hr hc hN₀ hN hθ hθ1 hm hrough R (hlegal side) hκ x
    (P false).hellingerSq (P true) ≤
      ∑ a : Option (incidenceGraph inc).ConnectedComponent,
        (propensityWitnessConditional Q ρ false S x₀ ℓ r h c w N N₀ θ ja b t τ
          hℓ hr hc hN₀ hN hθ hθ1 hm hrough R (hlegal false) hκ
          (fun i : {i // siteComponent inc i = a} => x i.val)).hellingerSq
        (propensityWitnessConditional Q ρ true S x₀ ℓ r h c w N N₀ θ ja b t τ
          hℓ hr hc hN₀ hN hθ hθ1 hm hrough R (hlegal true) hκ
          (fun i : {i // siteComponent inc i = a} => x i.val)) := by
  let F := fun z : (S → ℕ) × (activeBlocks (d := d) ℓ h → Bool) =>
    physicalCarrierProfile (ι := Fin Q) (D := 1) x₀ ℓ r h c w N N₀ θ
      hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S z.1) z.2
  let kernel := fun (side : Bool) (k : S) ζ n => if side then paperCoefficientLaw Q else (R k).kernel ζ n
  let fields := fun (side : Bool) (z : ((S → ℕ) × (activeBlocks (d := d) ℓ h → Bool)) ×
      (S → MomentGrid (CoefficientExponent d Q) (4 * Q))) =>
    roughPropensityFields side S (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S z.2 k))
      x₀ ℓ r h ja b t z.1.2
  have hk : ∀ side k ζ ζ' n, (∀ j ∈ carrierLocalSigns x₀ ℓ r h k.val, ζ j = ζ' j) →
      kernel side k ζ n = kernel side k ζ' n := by
    intro side k ζ ζ' n he
    cases side with
    | false => exact congrArg (fun f => f n) ((R k).kernel_local ζ ζ' he)
    | true => rfl
  exact rawCarrierConditional_component_hellinger F hθ hθ1 S x₀ r (fun k => (R k).law)
    kernel fields (fun side z => hlegal side z.1.2 z.2) hκ x
    (fun i (k : S) => x i ∈ carrierBox x₀ r k.val)
    (fun i => physicalLocalSigns x₀ ℓ h (x i)) (fun k => carrierLocalSigns x₀ ℓ r h k.val) hk
    (physicalDesign_observation_local x₀ ℓ r h c w N N₀ θ hℓ hr hc hN₀ hN hm hrough hθ S x)
    (fun side y => roughPropensity_observation_local side S (paperCoefficientAtoms Q ρ)
      x₀ ℓ r h ja b t hr x y)

end CausalLowerbound.PartC

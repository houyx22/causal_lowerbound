import CausalLowerbound.PartC.PhysicalDesignLocality

/-! Exact factorization of the actual unnormalized design-weighted
observation mixture. The input cell locality has been proved for both
mixed parameter families in MixedObservationLocality. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] incidenceComponentFintype
variable {d ι V Ω : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V] [Fintype Ω] [Inhabited Ω] {D : ℕ}

set_option maxHeartbeats 1200000 in
theorem physical_raw_observation_factorization (x₀ : d → ℝ) (ℓ r h : ℝ)
    (c w N N₀ θ : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀)
    (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (H : S → DiscreteLaw ℕ)
    (kernel : S → (activeBlocks (d := d) ℓ h → Bool) → ℕ → FiniteLaw Ω)
    (hkernel : ∀ k ζ ζ' n, (∀ j ∈ carrierLocalSigns x₀ ℓ r h k.val, ζ j = ζ' j) →
      kernel k ζ n = kernel k ζ' n)
    (fields : (activeBlocks (d := d) ℓ h → Bool) → (S → Ω) → NuisanceFields d)
    (x : V → d → ℝ) (y : V → Bool × Bool)
    (hcell : SharedObservationLocal (physicalSharedIncidence S x₀ ℓ r h x)
      (fun i ζ _ u => nuisanceCellMass (fields ζ u) (x i) (y i)))
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ} (hκ : 0 ≤ κ)
    (hlegal : ∀ ζ u, (fields ζ u).Legal α β γ Lπ L₀ Lτ κ) :
    let profile := fun labels ζ => physicalCarrierProfile (ι := ι) (D := D)
      x₀ ℓ r h c w N N₀ θ hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S labels) ζ
    let inc := physicalSharedIncidence S x₀ ℓ r h x
    let f := fun i ζ labels u => (profile labels ζ).product S x₀ r (x i) *
      nuisanceCellMass (fields ζ u) (x i) (y i)
    (signBlockPrior H kernel).expect (fun z =>
      (∏ i, (profile z.1.1 z.1.2).product S x₀ r (x i)) *
        ∏ i, nuisanceCellMass (fields z.1.2 z.2) (x i) (y i)) =
      ∏ a : Option (incidenceGraph inc).ConnectedComponent,
        independentSigns.expect (fun ζ =>
          (DiscreteLaw.independent (fun k : {k // componentBlockOwner inc k = a} => H k.val)).expect
            (signComponentValue (componentBlockOwner inc) kernel (sharedComponentIntegrand inc f) a ζ)) := by
  let profile := fun labels ζ => physicalCarrierProfile (ι := ι) (D := D)
    x₀ ℓ r h c w N N₀ θ hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S labels) ζ
  let inc := physicalSharedIncidence S x₀ ℓ r h x
  let design := fun i ζ labels (_ : S → Ω) => (profile labels ζ).product S x₀ r (x i)
  let cell := fun i ζ (_ : S → ℕ) u => nuisanceCellMass (fields ζ u) (x i) (y i)
  have hd : SharedObservationLocal inc design :=
    physicalDesign_observation_local x₀ ℓ r h c w N N₀ θ hℓ hr hc hN₀ hN hm hrough hθ S x
  have hf := SharedObservationLocal.mul inc design cell hd hcell
  have hb (i : V) (ζ : activeBlocks (d := d) ℓ h → Bool) (labels : S → ℕ) (u : S → Ω) :
      |design i ζ labels u * cell i ζ labels u| ≤ (1 + θ) ^ (5 ^ Fintype.card d) :=
    CarrierProfile.product_cellMass_bound (profile labels ζ) hθ hθ1 S x₀ r
      (fields ζ u) (x i) (y i) (hlegal ζ u) hκ
  have he := shared_observation_factorization H kernel
    (fun i (k : S) => x i ∈ carrierBox x₀ r k.val)
    (fun i => physicalLocalSigns x₀ ℓ h (x i))
    (fun k => carrierLocalSigns x₀ ℓ r h k.val) hkernel
    (fun i ζ labels u => design i ζ labels u * cell i ζ labels u) hf
    ((1 + θ) ^ (5 ^ Fintype.card d)) hb
  simpa only [design, cell, Finset.prod_mul_distrib] using he

end CausalLowerbound.PartC

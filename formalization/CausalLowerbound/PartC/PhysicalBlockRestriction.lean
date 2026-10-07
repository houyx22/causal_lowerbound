import CausalLowerbound.PartC.RawPropensityComparison

/-! Remove blocks not incident to the retained observations. The actual
design product, carried field, binary cells, and raw propensity likelihood
are preserved under the same restriction of the label and coefficient draw. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I Ω ι : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]
  [Fintype Ω] [Inhabited Ω] [Fintype ι] [DecidableEq ι] {D : ℕ} {θ : ℝ}

theorem CarrierProfile.product_restrict (F : CarrierProfile d θ)
    (S T : Finset (d → ℤ)) (hTS : T ⊆ S) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ)
    (hcover : ∀ k ∈ S, x ∈ carrierBox x₀ r k → k ∈ T) :
    F.product S x₀ r x = F.product T x₀ r x := by
  symm
  apply Finset.prod_subset hTS
  intro k hkS hkT
  exact if_neg (fun hx => hkT (hcover k hkS hx))

theorem carriedField_restrict (Q : ℕ) (S T : Finset (d → ℤ)) (hTS : T ⊆ S)
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r)
    (x : d → ℝ) (hcover : ∀ k ∈ S, x ∈ carrierBox x₀ r k → k ∈ T) :
    carriedField S U x₀ r x = carriedField T U x₀ r x := by
  rw [carriedField_eq_physical _ _ _ _ hr, carriedField_eq_physical _ _ _ _ hr]
  symm
  apply Finset.sum_subset hTS
  intro k hkS hkT
  have hz : linearPartition (localCoordinate x₀ r k x) = 0 := by
    by_contra hn
    exact hkT (hcover k hkS (linearPartition_nonzero_mem_carrierBox x₀ r k x hn))
  change linearPartition (localCoordinate x₀ r k x) * _ = 0
  rw [hz, zero_mul]

theorem carriedField_restrict_sample (Q : ℕ) (S T : Finset (d → ℤ)) (hTS : T ⊆ S)
    (atoms : Ω → CoefficientExponent d Q → ℝ) (ξ : S → Ω)
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (x : d → ℝ)
    (hcover : ∀ k ∈ S, x ∈ carrierBox x₀ r k → k ∈ T) :
    carriedField S (fun k => atoms (extendBlockSample S ξ k)) x₀ r x =
      carriedField T (fun k => atoms (extendBlockSample T (fun k : T => ξ ⟨k.val, hTS k.property⟩) k)) x₀ r x := by
  rw [carriedField_restrict Q S T hTS _ x₀ r hr x hcover]
  unfold carriedField
  apply Finset.sum_congr rfl
  intro k hk
  simp only [extendBlockSample, dif_pos hk, dif_pos (hTS hk)]

theorem physicalCarrierProfile_product_restrict (x₀ : d → ℝ) (ℓ r h c w N N₀ θ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀) (hθ : 0 ≤ θ)
    (S T : Finset (d → ℤ)) (hTS : T ⊆ S) (labels : S → ℕ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ)
    (hcover : ∀ k ∈ S, x ∈ carrierBox x₀ r k → k ∈ T) :
    (physicalCarrierProfile (ι := ι) (D := D) x₀ ℓ r h c w N N₀ θ
      hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S labels) ζ).product S x₀ r x =
    (physicalCarrierProfile (ι := ι) (D := D) x₀ ℓ r h c w N N₀ θ
      hℓ hr hc hN₀ hN hm hrough hθ
        (extendBlockSample T (fun k : T => labels ⟨k.val, hTS k.property⟩)) ζ).product T x₀ r x := by
  rw [CarrierProfile.product_restrict _ S T hTS x₀ r x hcover]
  unfold CarrierProfile.product
  apply Finset.prod_congr rfl
  intro k hk
  simp only [CarrierProfile.factor, physicalCarrierProfile, extendBlockSample,
    dif_pos hk, dif_pos (hTS hk)]

theorem roughPropensity_cell_restrict_sample (Q : ℕ) (side : Bool)
    (S T : Finset (d → ℤ)) (hTS : T ⊆ S) (atoms : Ω → CoefficientExponent d Q → ℝ)
    (ξ : S → Ω) (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (hr : 0 < r)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ) (y : Bool × Bool)
    (hcover : ∀ k ∈ S, x ∈ carrierBox x₀ r k → k ∈ T) :
    nuisanceCellMass (roughPropensityFields side S (fun k => atoms (extendBlockSample S ξ k))
      x₀ ℓ r h ja b t ζ) x y =
    nuisanceCellMass (roughPropensityFields side T
      (fun k => atoms (extendBlockSample T (fun k : T => ξ ⟨k.val, hTS k.property⟩) k))
      x₀ ℓ r h ja b t ζ) x y := by
  unfold nuisanceCellMass
  rw [roughPropensityFields_likelihood, roughPropensityFields_likelihood,
    carriedField_restrict_sample Q S T hTS atoms ξ x₀ r hr x hcover]

theorem physicalPropensityRawLikelihood_restrict
    (Q : ℕ) (ρ : ℝ) (side : Bool) (S T : Finset (d → ℤ)) (hTS : T ⊆ S) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ ja b t : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀) (hθ : 0 ≤ θ)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hcover : ∀ i k, k ∈ S → x i ∈ carrierBox x₀ r k → k ∈ T)
    (v : ((S → ℕ) × (activeBlocks (d := d) ℓ h → Bool)) ×
      (S → MomentGrid (CoefficientExponent d Q) (4 * Q))) :
    physicalPropensityRawLikelihood Q ρ side S x₀ ℓ r h c w N N₀ θ ja b t
      hℓ hr hc hN₀ hN hm hrough hθ x y v =
    physicalPropensityRawLikelihood Q ρ side T x₀ ℓ r h c w N N₀ θ ja b t
      hℓ hr hc hN₀ hN hm hrough hθ x y
      ((fun k : T => v.1.1 ⟨k.val, hTS k.property⟩, v.1.2), fun k : T => v.2 ⟨k.val, hTS k.property⟩) := by
  unfold physicalPropensityRawLikelihood
  apply Finset.prod_congr rfl
  intro i _
  rw [physicalCarrierProfile_product_restrict x₀ ℓ r h c w N N₀ θ
    hℓ hr hc hN₀ hN hm hrough hθ S T hTS v.1.1 v.1.2 (x i) (hcover i)]
  rw [roughPropensity_cell_restrict_sample Q side S T hTS (paperCoefficientAtoms Q ρ) v.2
    x₀ ℓ r h ja b t hr v.1.2 (x i) (y i) (hcover i)]

end CausalLowerbound.PartC

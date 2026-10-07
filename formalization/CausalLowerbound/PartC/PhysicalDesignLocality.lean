import CausalLowerbound.PartC.PhysicalCarrierLocality
import CausalLowerbound.PartC.MixedObservationLocality

/-! The actual shared-sign design product is local on the enlarged graph.
Multiplying it by a true binary cell probability preserves this locality
and a uniform bound independent of the total number of carrier blocks. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d ι V Ω : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V] [Fintype Ω] [Inhabited Ω] {D : ℕ}

theorem carrierCoordinate_mem_cube (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) (x : d → ℝ)
    (hx : x ∈ carrierBox x₀ r k) :
    carrierCoordinate (localCoordinate x₀ r k x) ∈ Set.Icc (0 : d → ℝ) 1 := by
  constructor <;> intro a
  · have ha : (-2 : ℝ) ≤ localCoordinate x₀ r k x a := hx.1 a
    change 0 ≤ localCoordinate x₀ r k x a / 4 + 1 / 2
    linarith
  · have ha : localCoordinate x₀ r k x a ≤ (2 : ℝ) := hx.2 a
    change localCoordinate x₀ r k x a / 4 + 1 / 2 ≤ 1
    linarith

theorem physicalCarrierProfile_product_local_congr (x₀ : d → ℝ) (ℓ r h : ℝ)
    (c w N N₀ θ : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀)
    (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hθ : 0 ≤ θ)
    (S : Finset (d → ℤ)) (labels labels' : S → ℕ)
    (ζ ζ' : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ)
    (hlabels : ∀ k : S, x ∈ carrierBox x₀ r k.val → labels k = labels' k)
    (hζ : ∀ k : S, x ∈ carrierBox x₀ r k.val →
      ∀ j ∈ carrierLocalSigns x₀ ℓ r h k.val, ζ j = ζ' j) :
    (physicalCarrierProfile (ι := ι) (D := D) x₀ ℓ r h c w N N₀ θ hℓ hr hc hN₀ hN hm hrough hθ
      (extendBlockSample S labels) ζ).product S x₀ r x =
    (physicalCarrierProfile (ι := ι) (D := D) x₀ ℓ r h c w N N₀ θ hℓ hr hc hN₀ hN hm hrough hθ
      (extendBlockSample S labels') ζ').product S x₀ r x := by
  unfold CarrierProfile.product
  apply Finset.prod_congr rfl
  intro k hk
  unfold CarrierProfile.factor
  by_cases hx : x ∈ carrierBox x₀ r k
  · rw [if_pos hx, if_pos hx]
    change carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ
      (extendBlockSample S labels k) ζ (carrierCoordinate (localCoordinate x₀ r k x)) =
      carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ
      (extendBlockSample S labels' k) ζ' (carrierCoordinate (localCoordinate x₀ r k x))
    simp only [extendBlockSample, dif_pos hk, hlabels ⟨k, hk⟩ hx]
    exact carrierPhysicalDensity_local_congr x₀ ℓ r h hr.ne' k c w N θ hc _ ζ ζ'
      (hζ ⟨k, hk⟩ hx) _ (carrierCoordinate_mem_cube x₀ r k x hx)
  · rw [if_neg hx, if_neg hx]

theorem physicalDesign_observation_local (x₀ : d → ℝ) (ℓ r h : ℝ)
    (c w N N₀ θ : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀)
    (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hθ : 0 ≤ θ)
    (S : Finset (d → ℤ)) (x : V → d → ℝ) :
    SharedObservationLocal (physicalSharedIncidence S x₀ ℓ r h x)
      (fun i ζ labels (_ : S → Ω) =>
        (physicalCarrierProfile (ι := ι) (D := D) x₀ ℓ r h c w N N₀ θ hℓ hr hc hN₀ hN hm hrough hθ
          (extendBlockSample S labels) ζ).product S x₀ r (x i)) := by
  intro i ζ ζ' labels labels' _ _ hζ hlabels _
  exact physicalCarrierProfile_product_local_congr x₀ ℓ r h c w N N₀ θ
    hℓ hr hc hN₀ hN hm hrough hθ S labels labels' ζ ζ' (x i) hlabels
    (fun k hk j hj => hζ j (Or.inr ⟨k, hk, hj⟩))

theorem SharedObservationLocal.mul {K J : Type*} [Fintype K] [DecidableEq K]
    [Fintype J] [DecidableEq J] (inc : V → K ⊕ J → Prop)
    (f g : V → (J → Bool) → (K → ℕ) → (K → Ω) → ℝ)
    (hf : SharedObservationLocal inc f) (hg : SharedObservationLocal inc g) :
    SharedObservationLocal inc (fun i ζ labels u => f i ζ labels u * g i ζ labels u) := by
  intro i ζ ζ' labels labels' u u' hζ hl hu
  dsimp only
  rw [hf i ζ ζ' labels labels' u u' hζ hl hu, hg i ζ ζ' labels labels' u u' hζ hl hu]

theorem CarrierProfile.product_cellMass_bound {θ : ℝ} (F : CarrierProfile d θ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (fields : NuisanceFields d) (x : d → ℝ) (y : Bool × Bool)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ} (hlegal : fields.Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ) :
    |F.product S x₀ r x * nuisanceCellMass fields x y| ≤ (1 + θ) ^ (5 ^ Fintype.card d) := by
  have hp := F.product_bounds hθ hθ1 S x₀ r x
  have hnonneg : 0 ≤ F.product S x₀ r x := (pow_nonneg (sub_nonneg.mpr hθ1.le) _).trans hp.1
  rw [abs_mul, abs_of_nonneg hnonneg]
  calc
    _ ≤ F.product S x₀ r x * 1 := mul_le_mul_of_nonneg_left
      (nuisanceCellMass_abs_le_one fields x y hlegal hκ) hnonneg
    _ ≤ _ := by simpa only [mul_one] using hp.2

end CausalLowerbound.PartC

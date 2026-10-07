import CausalLowerbound.PartC.SharedCarrierGeometry
import CausalLowerbound.PartC.SharedObservationFactorization
import CausalLowerbound.PartC.SupportedAssignmentGeometry

/-! Identify each observed component's owned carrier labels with the
actual incident lattice blocks. This makes its block count depend only
on the number of observations and the fixed geometric overlap. -/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] incidenceComponentFintype
variable {d V K J : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]

theorem componentBlockOwner_eq_iff (inc : V → K ⊕ J → Prop)
    (c : Option (incidenceGraph inc).ConnectedComponent) (hc : c ≠ none) (k : K) :
    componentBlockOwner inc k = c ↔ ∃ i, siteComponent inc i = c ∧ inc i (Sum.inl k) := by
  constructor
  · intro hk
    by_cases he : ∃ i, inc i (Sum.inl k)
    · obtain ⟨i, hi⟩ := he
      exact ⟨i, (blockComponent_of_inc inc i (Sum.inl k) hi).symm.trans hk, hi⟩
    · have hz : componentBlockOwner inc k = none := by
        simp only [componentBlockOwner, blockComponent, dif_neg he]
      exact (hc (hk.symm.trans hz)).elim
  · rintro ⟨i, hi, hik⟩
    exact (blockComponent_of_inc inc i (Sum.inl k) hik).trans hi

def physicalComponentBlocksEquiv (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h : ℝ)
    (x : V → d → ℝ)
    (c : Option (incidenceGraph (physicalSharedIncidence S x₀ ℓ r h x)).ConnectedComponent)
    (hc : c ≠ none) :
    {k : S // componentBlockOwner (physicalSharedIncidence S x₀ ℓ r h x) k = c} ≃
      configurationBlocks S x₀ r
        (fun i : {i // siteComponent (physicalSharedIncidence S x₀ ℓ r h x) i = c} => x i.val) where
  toFun k := ⟨k.val.val, by
    obtain ⟨i, hi, hik⟩ := (componentBlockOwner_eq_iff _ c hc k.val).mp k.property
    exact (mem_configurationBlocks S x₀ r _ k.val.val).mpr ⟨k.val.property, ⟨i, hi⟩, hik⟩⟩
  invFun k := ⟨⟨k.val, ((mem_configurationBlocks S x₀ r _ k.val).mp k.property).1⟩, by
    obtain ⟨i, hi⟩ := ((mem_configurationBlocks S x₀ r _ k.val).mp k.property).2
    exact (componentBlockOwner_eq_iff _ c hc _).mpr ⟨i.val, i.property, hi⟩⟩
  left_inv k := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv k := by apply Subtype.ext; rfl

theorem physical_component_block_card_le (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h : ℝ)
    (x : V → d → ℝ)
    (c : Option (incidenceGraph (physicalSharedIncidence S x₀ ℓ r h x)).ConnectedComponent)
    (hc : c ≠ none) :
    Fintype.card {k : S // componentBlockOwner (physicalSharedIncidence S x₀ ℓ r h x) k = c} ≤
      Fintype.card {i // siteComponent (physicalSharedIncidence S x₀ ℓ r h x) i = c} * 5 ^ Fintype.card d := by
  calc
    _ = (configurationBlocks S x₀ r
        (fun i : {i // siteComponent (physicalSharedIncidence S x₀ ℓ r h x) i = c} => x i.val)).card := by
      simpa only [Fintype.card_coe] using Fintype.card_congr (physicalComponentBlocksEquiv S x₀ ℓ r h x c hc)
    _ ≤ _ := configurationBlocks_card_le S x₀ r _

end CausalLowerbound.PartC

import CausalLowerbound.PartB.ComponentCarrierRestriction

/-! Actual component sizes, including the empty fiber for unused blocks. -/
noncomputable section
set_option autoImplicit false
open scoped Classical
namespace CausalLowerbound.PartB
attribute [local instance] incidenceComponentFintype
variable {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]

theorem siteComponent_card_le (inc : V → K → Prop) (Q : ℕ)
    (hQ : ∀ root, (reachableVertices (incidenceGraph inc) root).card ≤ Q)
    (c : Option (incidenceGraph inc).ConnectedComponent) :
    Fintype.card {i // siteComponent inc i = c} ≤ Q := by
  by_cases hn : Nonempty {i // siteComponent inc i = c}
  · obtain ⟨root⟩ := hn
    let f : {i // siteComponent inc i = c} → reachableVertices (incidenceGraph inc) root.val :=
      fun i => ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        SimpleGraph.ConnectedComponent.exact (Option.some.inj (root.property.trans i.property.symm))⟩⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      exact congrArg (fun t : reachableVertices (incidenceGraph inc) root.val => t.val) hij
    exact (Fintype.card_le_of_injective f hf).trans (by
      simpa only [Fintype.card_coe] using hQ root.val)
  · haveI : IsEmpty {i // siteComponent inc i = c} := not_nonempty_iff.mp hn
    simp

namespace ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt physicalComponentFintype
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem component_fiber_small_off_largeCluster (n Q : ℕ) (hQ : 1 ≤ Q)
    (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hrh : r ≤ h)
    (x : Fin n → d → ℝ) (hx : x ∉ largeClusterEvent n Q x₀ r h)
    (c : Option (observationGraph (activeBlocks r h) x₀ r x).ConnectedComponent) :
    Fintype.card {i // siteComponent (fun j (k : activeBlocks (d := d) r h) =>
      x j ∈ carrierBox x₀ r k.val) i = c} ≤ Q :=
  siteComponent_card_le _ Q (component_size_le_off_largeCluster n Q hQ x₀ r h hr hrh x hx) c

theorem component_carrier_card_le (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) {n m : ℕ}
    (x : Fin n → d → ℝ) (c : Option (observationGraph S x₀ r x).ConnectedComponent)
    (e : Fin m ≃ {i // siteComponent (fun j (k : S) => x j ∈ carrierBox x₀ r k.val) i = c})
    (k : S) : (carrierSites x₀ r k.val (componentConfiguration S x₀ r x c e)).card ≤ m := by
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)

end ShellGeometry
end CausalLowerbound.PartB

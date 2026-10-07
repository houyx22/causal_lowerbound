import CausalLowerbound.PartB.ComponentFactorization

/-! An observation reads its own signs and every sign read by an incident
carrier. Connected components of this enlarged graph have disjoint sign
sets, including the dependencies of the local coefficient kernels. -/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace CausalLowerbound.PartC
open PartB
variable {V K J : Type*} [Fintype V] [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]

def sharedSignIncidence (blockInc : V → K → Prop) (siteSigns : V → Finset J)
    (blockSigns : K → Finset J) : V → K ⊕ J → Prop
  | i, Sum.inl k => blockInc i k
  | i, Sum.inr j => j ∈ siteSigns i ∨ ∃ k, blockInc i k ∧ j ∈ blockSigns k

def componentSignSet (inc : V → K ⊕ J → Prop)
    (c : Option (incidenceGraph inc).ConnectedComponent) : Finset J :=
  Finset.univ.filter (fun j => ∃ i, siteComponent inc i = c ∧ inc i (Sum.inr j))

theorem mem_componentSignSet (inc : V → K ⊕ J → Prop)
    (c : Option (incidenceGraph inc).ConnectedComponent) (j : J) :
    j ∈ componentSignSet inc c ↔ ∃ i, siteComponent inc i = c ∧ inc i (Sum.inr j) := by
  simp only [componentSignSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem componentSignSet_disjoint (inc : V → K ⊕ J → Prop)
    (c c' : Option (incidenceGraph inc).ConnectedComponent) (hne : c ≠ c') :
    Disjoint (componentSignSet inc c) (componentSignSet inc c') := by
  apply Finset.disjoint_left.mpr
  intro j hj hj'
  obtain ⟨i, hi, hij⟩ := (mem_componentSignSet inc c j).mp hj
  obtain ⟨i', hi', hi'j⟩ := (mem_componentSignSet inc c' j).mp hj'
  have he : siteComponent inc i = siteComponent inc i' :=
    congrArg some (common_label_same_component inc i i' (Sum.inr j) hij hi'j)
  exact hne (hi.symm.trans (he.trans hi'))

theorem componentSignSet_none (inc : V → K ⊕ J → Prop) :
    componentSignSet inc none = ∅ := by
  simp [componentSignSet, siteComponent]

theorem siteSigns_subset_component (blockInc : V → K → Prop) (siteSigns : V → Finset J)
    (blockSigns : K → Finset J) (i : V) :
    siteSigns i ⊆ componentSignSet (sharedSignIncidence blockInc siteSigns blockSigns)
      (siteComponent (sharedSignIncidence blockInc siteSigns blockSigns) i) := by
  intro j hj
  exact (mem_componentSignSet _ _ j).mpr ⟨i, rfl, Or.inl hj⟩

theorem blockSigns_subset_component (blockInc : V → K → Prop) (siteSigns : V → Finset J)
    (blockSigns : K → Finset J) (k : K)
    (c : Option (incidenceGraph (sharedSignIncidence blockInc siteSigns blockSigns)).ConnectedComponent)
    (howner : blockComponent (sharedSignIncidence blockInc siteSigns blockSigns) (Sum.inl k) = c)
    (hc : c ≠ none) :
    blockSigns k ⊆ componentSignSet (sharedSignIncidence blockInc siteSigns blockSigns) c := by
  let inc := sharedSignIncidence blockInc siteSigns blockSigns
  have he : ∃ i, blockInc i k := by
    by_contra hn
    have hnone : blockComponent inc (Sum.inl k) = none := by
      simp only [blockComponent, inc, sharedSignIncidence, hn, dite_false]
    exact hc (howner.symm.trans hnone)
  obtain ⟨i, hi⟩ := he
  intro j hj
  refine (mem_componentSignSet inc c j).mpr ⟨i, ?_, Or.inr ⟨k, hi, hj⟩⟩
  exact (blockComponent_of_inc inc i (Sum.inl k) hi).symm.trans howner

end CausalLowerbound.PartC

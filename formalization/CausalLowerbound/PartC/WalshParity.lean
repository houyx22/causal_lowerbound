import CausalLowerbound.PartC.WalshProduct
import Mathlib.Data.Finset.Fold

/-! Finite parity unions and simultaneous sign reflection. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators symmDiff

namespace CausalLowerbound.PartC.Walsh

variable {ι J : Type*} [Fintype J] [DecidableEq J]

def flip (ζ : J → Bool) (j : J) : Bool := !(ζ j)

@[simp] theorem flip_flip (ζ : J → Bool) : flip (flip ζ) = ζ := by
  funext j
  simp [flip]

theorem character_flip (S : Finset J) (ζ : J → Bool) :
    character S (flip ζ) = (-1) ^ S.card * character S ζ := by
  have hs (b : Bool) : PartB.sign (!b) = -(PartB.sign b) := by
    cases b <;> norm_num [PartB.sign]
  simp only [character, flip, hs, Finset.prod_neg]

def parityUnion [Fintype ι] (f : ι → Finset J) : Finset J :=
  Finset.univ.fold (fun S T : Finset J => S ∆ T) ∅ f

theorem character_parityUnion [Fintype ι] (f : ι → Finset J) (ζ : J → Bool) :
    character (parityUnion f) ζ = ∏ i, character (f i) ζ := by
  classical
  have h (s : Finset ι) : character (s.fold (fun S T : Finset J => S ∆ T) ∅ f) ζ =
      ∏ i ∈ s, character (f i) ζ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.fold_insert hi, character_symmDiff, Finset.prod_insert hi, ih]
  exact h Finset.univ

theorem mem_parityUnion [Fintype ι] (f : ι → Finset J) {j : J}
    (hj : j ∈ parityUnion f) : ∃ i, j ∈ f i := by
  classical
  have h (s : Finset ι) : j ∈ s.fold (fun S T : Finset J => S ∆ T) ∅ f →
      ∃ i ∈ s, j ∈ f i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.fold_insert hi]
      intro hj
      rcases Finset.mem_symmDiff.mp hj with ⟨hji, _⟩ | ⟨hjs, _⟩
      · exact ⟨i, Finset.mem_insert_self _ _, hji⟩
      · obtain ⟨k, hks, hjk⟩ := ih hjs
        exact ⟨k, Finset.mem_insert_of_mem hks, hjk⟩
  obtain ⟨i, _, hi⟩ := h Finset.univ hj
  exact ⟨i, hi⟩

end CausalLowerbound.PartC.Walsh

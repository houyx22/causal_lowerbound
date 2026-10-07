import CausalLowerbound.PartB.CompleteGraph
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

def completeEdgeTriangle (Q : ℕ) : CompleteEdge (Fin Q) ≃ (j : Fin Q) × Fin j.val where
  toFun e := ⟨e.val.2, ⟨e.val.1.val, e.property⟩⟩
  invFun p := ⟨(⟨p.2.val, lt_trans p.2.isLt p.1.isLt⟩, p.1), p.2.isLt⟩
  left_inv e := by rfl
  right_inv p := by rfl

theorem completeEdge_card (Q : ℕ) : Fintype.card (CompleteEdge (Fin Q)) = Q.choose 2 := by
  rw [Fintype.card_congr (completeEdgeTriangle Q), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id, Nat.choose_two_right]

end CausalLowerbound.PartB.ShellGeometry

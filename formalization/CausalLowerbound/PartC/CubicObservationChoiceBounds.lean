import CausalLowerbound.PartC.CubicObservationChoices

/-! Finite combinatorial bounds for the complete cubic observation
expansion. They depend only on the observation and carrier-block counts. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

theorem cubicObservationChoice_card :
    Fintype.card (CubicObservationChoice K) =
      1 + Fintype.card K + (Fintype.card K) ^ 2 + (Fintype.card K) ^ 3 := by
  simp [CubicObservationChoice, Fintype.card_sigma, Fintype.card_fun, Fin.sum_univ_succ]
  <;> omega

theorem cubicObservationChoices_card :
    Fintype.card (I → CubicObservationChoice K) =
      (1 + Fintype.card K + (Fintype.card K) ^ 2 + (Fintype.card K) ^ 3) ^ Fintype.card I := by
  rw [Fintype.card_fun, cubicObservationChoice_card]

theorem cubicObservationChoiceDegree_le (s : I → CubicObservationChoice K) :
    cubicObservationChoiceDegree s ≤ 3 * Fintype.card I := by
  rw [cubicObservationChoiceDegree_eq]
  calc
    _ ≤ ∑ _i : I, 3 := Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (s i).1.isLt)
    _ = _ := by simp [mul_comm]

theorem cubicObservationChoiceDegree_zero_iff (s : I → CubicObservationChoice K) :
    cubicObservationChoiceDegree s = 0 ↔ ∀ i, (s i).1 = 0 := by
  simp only [cubicObservationChoiceDegree_eq, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies]
  constructor
  · intro hs i
    exact Fin.ext (hs i)
  · intro hs i
    exact congrArg Fin.val (hs i)

theorem cubicObservationChoiceWeight_bound (δ : I → K → ℝ) (C : ℝ)
    (hδ : ∀ i k, |δ i k| ≤ C) (s : I → CubicObservationChoice K) :
    |cubicObservationChoiceWeight δ s| ≤ C ^ cubicObservationChoiceDegree s := by
  rw [cubicObservationChoiceWeight, Finset.abs_prod]
  calc
    _ ≤ ∏ _p : CubicObservationPositions s, C :=
      Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun p _ => hδ p.1 ((s p.1).2 p.2))
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, cubicObservationChoiceDegree]

end CausalLowerbound.PartC

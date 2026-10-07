import CausalLowerbound.PartC.CompletedOutcomeRows

/-! Embed the cubic input degrees of each completed carrier in the
common observation set. Nonincident observations have input degree zero;
nonzero Taylor degrees are restricted to incident observations. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative
variable {d V J I G : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype G]

def retainedOutcomeRowDegree (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (r : Degree V 3) (i : I) : Fin 4 :=
  if hi : P i then r (e (Sum.inl ⟨i, hi⟩)) else 0

theorem retained_outcome_row_product (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (r : Degree V 3) (f : Degree I 3) (hf : ∀ i, ¬P i → f i = 0)
    (κ a : I → ℝ) :
    (∏ i : {i // P i}, if f i.val = 0 then a i.val ^ (r (e (Sum.inl i))).val else
      outcomeMoment (κ i.val) (r (e (Sum.inl i))) * a i.val ^ (f i.val).val) =
      ∏ i : I, if f i = 0 then a i ^ (retainedOutcomeRowDegree P e r i).val else
        outcomeMoment (κ i) (retainedOutcomeRowDegree P e r i) * a i ^ (f i).val := by
  let F := fun i : I => if f i = 0 then a i ^ (retainedOutcomeRowDegree P e r i).val else
    outcomeMoment (κ i) (retainedOutcomeRowDegree P e r i) * a i ^ (f i).val
  have hret (i : {i // P i}) : F i.val =
      if f i.val = 0 then a i.val ^ (r (e (Sum.inl i))).val else
        outcomeMoment (κ i.val) (r (e (Sum.inl i))) * a i.val ^ (f i.val).val := by
    simp only [F, retainedOutcomeRowDegree, dif_pos i.property]
  have hout (i : {i // ¬P i}) : F i.val = 1 := by
    simp only [F, hf i.val i.property, if_true, retainedOutcomeRowDegree,
      dif_neg i.property, Fin.val_zero, pow_zero]
  change _ = ∏ i, F i
  rw [← Fintype.prod_subtype_mul_prod_subtype P F]
  simp only [hret, hout, Finset.prod_const_one, mul_one]

theorem outcomePatternWeight_retained_rows
    (P : I → Prop) (e : {i // P i} ⊕ G ≃ V) (κ : V → ℝ) (v a : I → ℝ)
    (hκ : ∀ i : {i // P i}, κ (e (Sum.inl i)) = v i.val)
    (W : Array d V J 3) (u : V × d → ℝ) (ζ : J → Bool) (g : G → ℝ)
    (f : Degree I 3) (hf : ∀ i, ¬P i → f i = 0) :
    outcomePatternWeight κ W u (completedSites e (fun i => a i.val) g) ζ
      (completedSites e (fun i => f i.val) (fun _ => 0)) =
      ∑ r : Row V J 3, completedOutcomeRowCoefficient W u ζ e g r *
        ∏ i, if f i = 0 then a i ^ (retainedOutcomeRowDegree P e r.1 i).val else
          outcomeMoment (v i) (retainedOutcomeRowDegree P e r.1 i) * a i ^ (f i).val := by
  rw [outcomePatternWeight_completed_rows]
  apply Finset.sum_congr rfl
  intro r _
  apply congrArg (fun z : ℝ => completedOutcomeRowCoefficient W u ζ e g r * z)
  simp only [hκ]
  exact retained_outcome_row_product P e r.1 f hf v a

theorem pointValue_retained_outcome_rows (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (a : I → ℝ) (W : Array d V J 3) (u : V × d → ℝ) (ζ : J → Bool) (g : G → ℝ) :
    pointValue (torusProjection u) (completedSites e (fun i => a i.val) g) ζ W =
      ∑ r : Row V J 3, completedOutcomeRowCoefficient W u ζ e g r *
        ∏ i, a i ^ (retainedOutcomeRowDegree P e r.1 i).val := by
  rw [pointValue_completed_outcome_rows]
  apply Finset.sum_congr rfl
  intro r _
  apply congrArg (fun z : ℝ => completedOutcomeRowCoefficient W u ζ e g r * z)
  simpa only [if_true] using
    retained_outcome_row_product P e r.1 (fun _ => 0) (by simp) (fun _ => 0) a

end CausalLowerbound.PartC

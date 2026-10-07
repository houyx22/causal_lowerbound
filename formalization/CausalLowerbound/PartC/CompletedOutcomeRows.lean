import CausalLowerbound.PartC.OutcomePolynomialTarget
import CausalLowerbound.PartC.UnitCubeGhosts

/-! The cubic completed carrier keeps all ghost powers in its row
coefficient. A retained Taylor pattern has degree zero at every ghost. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative
variable {d V J I G : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype G]

def completedOutcomeRowCoefficient (W : Array d V J 3) (u : V × d → ℝ) (ζ : J → Bool)
    (e : I ⊕ G ≃ V) (g : G → ℝ) (r : Row V J 3) : ℝ :=
  Walsh.character r.2 ζ * (toContinuous (W r) (torusProjection u)).re *
    ∏ j, g j ^ (r.1 (e (Sum.inr j))).val

theorem completed_outcome_slot_product (κ : V → ℝ) (e : I ⊕ G ≃ V)
    (a : I → ℝ) (g : G → ℝ) (r : Degree V 3) (f : Degree I 3) :
    (∏ v, outcomeSlotFactor (completedSites e f (fun _ => 0)) κ (completedSites e a g) r v) =
      (∏ i, if f i = 0 then a i ^ (r (e (Sum.inl i))).val else
        outcomeMoment (κ (e (Sum.inl i))) (r (e (Sum.inl i))) * a i ^ (f i).val) *
      ∏ j, g j ^ (r (e (Sum.inr j))).val := by
  rw [← e.prod_comp (fun v => outcomeSlotFactor (completedSites e f (fun _ => 0)) κ
    (completedSites e a g) r v)]
  simp only [Fintype.prod_sum_type, outcomeSlotFactor, completedSites_retained,
    completedSites_ghost, if_true]

theorem outcomePatternWeight_completed_rows (κ : V → ℝ) (W : Array d V J 3)
    (u : V × d → ℝ) (ζ : J → Bool) (e : I ⊕ G ≃ V)
    (a : I → ℝ) (g : G → ℝ) (f : Degree I 3) :
    outcomePatternWeight κ W u (completedSites e a g) ζ (completedSites e f (fun _ => 0)) =
      ∑ r : Row V J 3, completedOutcomeRowCoefficient W u ζ e g r *
        ∏ i, if f i = 0 then a i ^ (r.1 (e (Sum.inl i))).val else
          outcomeMoment (κ (e (Sum.inl i))) (r.1 (e (Sum.inl i))) * a i ^ (f i).val := by
  simp only [outcomePatternWeight, completed_outcome_slot_product, completedOutcomeRowCoefficient]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem completedSites_zero_degree (e : I ⊕ G ≃ V) :
    completedSites e (fun _ : I => (0 : Fin 4)) (fun _ : G => 0) = fun _ : V => 0 := by
  funext v
  simp only [completedSites, Function.comp_apply]
  cases e.symm v <;> rfl

theorem pointValue_completed_outcome_rows (W : Array d V J 3)
    (u : V × d → ℝ) (ζ : J → Bool) (e : I ⊕ G ≃ V) (a : I → ℝ) (g : G → ℝ) :
    pointValue (torusProjection u) (completedSites e a g) ζ W =
      ∑ r : Row V J 3, completedOutcomeRowCoefficient W u ζ e g r *
        ∏ i, a i ^ (r.1 (e (Sum.inl i))).val := by
  have he := outcomePatternWeight_completed_rows (fun _ => 0) W u ζ e a g (fun _ => 0)
  rw [completedSites_zero_degree e, outcomePatternWeight_zero] at he
  simpa only [if_true] using he

end CausalLowerbound.PartC

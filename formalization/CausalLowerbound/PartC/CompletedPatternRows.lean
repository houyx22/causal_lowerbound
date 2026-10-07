import CausalLowerbound.PartC.PropensityPolynomialTarget
import CausalLowerbound.PartC.UnitCubeGhosts

/-! Split an actual completed representative into its retained-variable
rows. Ghost powers remain in the row coefficient, together with the
Fourier and frozen Walsh factors. No coefficient is dropped or normalized. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative
variable {d V J I G : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype G]

def completedRowCoefficient (W : Array d V J 1) (u : V × d → ℝ) (η : J → Bool)
    (e : I ⊕ G ≃ V) (g : G → ℝ) (r : Row V J 1) : ℝ :=
  Walsh.character r.2 η * (toContinuous (W r) (torusProjection u)).re *
    ∏ j, g j ^ (r.1 (e (Sum.inr j))).val

theorem completed_propensity_slot_product (κ : V → ℝ) (e : I ⊕ G ≃ V)
    (a : I → ℝ) (g : G → ℝ) (r : Degree V 1) (A : Finset I) :
    (∏ v, propensitySlotFactor (A.image (fun i => e (Sum.inl i))) κ (completedSites e a g) r v) =
      (∏ i, if i ∈ A then if r (e (Sum.inl i)) = 0 then a i else κ (e (Sum.inl i))
        else a i ^ (r (e (Sum.inl i))).val) *
      ∏ j, g j ^ (r (e (Sum.inr j))).val := by
  have hi (i : I) : e (Sum.inl i) ∈ A.image (fun i => e (Sum.inl i)) ↔ i ∈ A := by simp
  have hg (j : G) : e (Sum.inr j) ∉ A.image (fun i => e (Sum.inl i)) := by simp
  rw [← e.prod_comp (fun v => propensitySlotFactor (A.image (fun i => e (Sum.inl i))) κ
    (completedSites e a g) r v)]
  simp only [Fintype.prod_sum_type, propensitySlotFactor, hi, hg, if_false,
    completedSites_retained, completedSites_ghost]

theorem propensityPatternWeight_completed_rows (κ : V → ℝ) (W : Array d V J 1)
    (u : V × d → ℝ) (η : J → Bool) (e : I ⊕ G ≃ V)
    (a : I → ℝ) (g : G → ℝ) (A : Finset I) :
    propensityPatternWeight κ W u (completedSites e a g) η (A.image (fun i => e (Sum.inl i))) =
      ∑ r : Row V J 1, completedRowCoefficient W u η e g r *
        ∏ i, if i ∈ A then if r.1 (e (Sum.inl i)) = 0 then a i else κ (e (Sum.inl i))
          else a i ^ (r.1 (e (Sum.inl i))).val := by
  simp only [propensityPatternWeight, completed_propensity_slot_product, completedRowCoefficient]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem pointValue_completed_rows (W : Array d V J 1)
    (u : V × d → ℝ) (η : J → Bool) (e : I ⊕ G ≃ V) (a : I → ℝ) (g : G → ℝ) :
    pointValue (torusProjection u) (completedSites e a g) η W =
      ∑ r : Row V J 1, completedRowCoefficient W u η e g r *
        ∏ i, a i ^ (r.1 (e (Sum.inl i))).val := by
  simpa only [Finset.image_empty, propensityPatternWeight_empty, Finset.not_mem_empty, if_false] using
    propensityPatternWeight_completed_rows (fun _ => 0) W u η e a g ∅

end CausalLowerbound.PartC

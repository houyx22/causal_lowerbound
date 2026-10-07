import CausalLowerbound.PartC.CompletedPatternRows
import CausalLowerbound.PartC.NormalizedPropensityBridge

/-! Embed the retained rows of each completed carrier into the common
observation index set. Nonincident observations have degree zero. Selected
observations are required to be incident only in this pointwise identity;
the observation expansion supplies that fact whenever its coefficient is
nonzero. Ghost, Fourier, and Walsh factors stay in the coefficient. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative RoughPropensity
variable {d V J I G : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype G]

def retainedRowDegree (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (r : Degree V 1) (i : I) : ℕ :=
  if hi : P i then (r (e (Sum.inl ⟨i, hi⟩))).val else 0

theorem retainedRowDegree_le_one (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (r : Degree V 1) (i : I) : retainedRowDegree P e r i ≤ 1 := by
  unfold retainedRowDegree
  split_ifs with hi
  · exact Nat.le_of_lt_succ (r (e (Sum.inl ⟨i, hi⟩))).isLt
  · exact Nat.zero_le _

theorem retained_pattern_slot_image (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (slot : I → V) (hslot : ∀ i (hi : P i), slot i = e (Sum.inl ⟨i, hi⟩))
    (A : Finset I) (hA : ∀ i ∈ A, P i) :
    A.image slot = (A.subtype P).image (fun i => e (Sum.inl i)) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_subtype]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hA i hi⟩, hi, (hslot i (hA i hi)).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.val, hi, hslot i.val i.property⟩

theorem retained_pattern_row_product (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (r : Degree V 1) (A : Finset I) (hA : ∀ i ∈ A, P i)
    (scale ja v X : I → ℝ) :
    (∏ i : {i // P i}, if i.val ∈ A then
      if r (e (Sum.inl i)) = 0 then scale i.val * X i.val
        else scale i.val ^ 2 * ja i.val ^ 2 * v i.val ^ 2
      else (scale i.val * X i.val) ^ (r (e (Sum.inl i))).val) =
    ∏ i : I, if i ∈ A then normalizedSubstitution (retainedRowDegree P e r i)
      (scale i) (ja i) (v i) (X i) else (scale i * X i) ^ retainedRowDegree P e r i := by
  let f := fun i : I => if i ∈ A then normalizedSubstitution (retainedRowDegree P e r i)
    (scale i) (ja i) (v i) (X i) else (scale i * X i) ^ retainedRowDegree P e r i
  have hret (i : {i // P i}) : f i.val =
      if i.val ∈ A then if r (e (Sum.inl i)) = 0 then scale i.val * X i.val
        else scale i.val ^ 2 * ja i.val ^ 2 * v i.val ^ 2
      else (scale i.val * X i.val) ^ (r (e (Sum.inl i))).val := by
    simp only [f, retainedRowDegree, dif_pos i.property, normalizedSubstitution, Fin.val_eq_zero_iff]
  have hout (i : {i // ¬P i}) : f i.val = 1 := by
    have hi : i.val ∉ A := fun hi => i.property (hA i.val hi)
    simp only [f, if_neg hi, retainedRowDegree, dif_neg i.property, pow_zero]
  change _ = ∏ i, f i
  rw [← Fintype.prod_subtype_mul_prod_subtype P f]
  simp only [hret, hout, Finset.prod_const_one, mul_one]

theorem propensityPatternWeight_retained_rows
    (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (slot : I → V) (hslot : ∀ i (hi : P i), slot i = e (Sum.inl ⟨i, hi⟩))
    (κ : V → ℝ) (scale ja v X : I → ℝ)
    (hκ : ∀ i : {i // P i}, κ (e (Sum.inl i)) = scale i.val ^ 2 * ja i.val ^ 2 * v i.val ^ 2)
    (W : Array d V J 1) (u : V × d → ℝ) (η : J → Bool) (g : G → ℝ)
    (A : Finset I) (hA : ∀ i ∈ A, P i) :
    propensityPatternWeight κ W u (completedSites e (fun i => scale i.val * X i.val) g)
      η (A.image slot) =
      ∑ r : Row V J 1, completedRowCoefficient W u η e g r *
        ∏ i, if i ∈ A then normalizedSubstitution (retainedRowDegree P e r.1 i)
          (scale i) (ja i) (v i) (X i) else (scale i * X i) ^ retainedRowDegree P e r.1 i := by
  rw [retained_pattern_slot_image P e slot hslot A hA,
    propensityPatternWeight_completed_rows]
  apply Finset.sum_congr rfl
  intro r _
  apply congrArg (fun z : ℝ => completedRowCoefficient W u η e g r * z)
  simp only [Finset.mem_subtype, hκ]
  exact retained_pattern_row_product P e r.1 A hA scale ja v X

theorem pointValue_retained_rows (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (scale X : I → ℝ) (W : Array d V J 1) (u : V × d → ℝ)
    (η : J → Bool) (g : G → ℝ) :
    pointValue (torusProjection u) (completedSites e (fun i => scale i.val * X i.val) g) η W =
      ∑ r : Row V J 1, completedRowCoefficient W u η e g r *
        ∏ i, (scale i * X i) ^ retainedRowDegree P e r.1 i := by
  rw [pointValue_completed_rows]
  apply Finset.sum_congr rfl
  intro r _
  apply congrArg (fun z : ℝ => completedRowCoefficient W u η e g r * z)
  simpa only [Finset.not_mem_empty, if_false] using
    retained_pattern_row_product P e r.1 ∅ (by simp) scale (fun _ => 0) (fun _ => 0) X

end CausalLowerbound.PartC

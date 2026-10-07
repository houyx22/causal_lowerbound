import CausalLowerbound.PartC.WeightedPropensityPatterns
import CausalLowerbound.PartC.RepresentativeStability

/-! Stability of normalized selected-slot weights. Changing only unselected
variables costs the centered representative norm, with no power of the
normalization. This is the form needed for resampling ghost rough fields. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative
variable {d V J : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

theorem weightedPropensityPatternWeight_expansion (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 1) (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (S : Finset V) :
    weightedPropensityPatternWeight N κ W u z ζ S =
      ∑ r : Row V J 1, Walsh.character r.2 ζ * (toContinuous (W r) (torusProjection u)).re *
        ∏ i, (if i ∈ S then N else 1) * propensitySlotFactor S κ z r.1 i := by
  have hp (a : Degree V 1) : N ^ S.card * (∏ i, propensitySlotFactor S κ z a i) =
      ∏ i, (if i ∈ S then N else 1) * propensitySlotFactor S κ z a i := by
    rw [Finset.prod_mul_distrib]
    simp
  simp only [weightedPropensityPatternWeight, propensityPatternWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [← hp]
  ring

theorem weightedPropensitySlotFactor_bound (N : ℝ) (κ z : V → ℝ) (S : Finset V)
    (C : ℝ) (hC : 1 ≤ C) (hz : ∀ i, |z i| ≤ 1)
    (hNz : ∀ i, |N * z i| ≤ C) (hNκ : ∀ i, |N * κ i| ≤ C)
    (a : Degree V 1) (i : V) :
    |(if i ∈ S then N else 1) * propensitySlotFactor S κ z a i| ≤ C := by
  by_cases hi : i ∈ S
  · by_cases ha : a i = 0
    · simpa only [propensitySlotFactor, if_pos hi, if_pos ha] using hNz i
    · simpa only [propensitySlotFactor, if_pos hi, if_neg ha] using hNκ i
  · simp only [if_neg hi, propensitySlotFactor, one_mul, abs_pow]
    exact (pow_le_one₀ (abs_nonneg _) (hz i)).trans hC

theorem weightedPropensitySlotProduct_sub_bound (N : ℝ) (κ z z' : V → ℝ)
    (S : Finset V) (hS : ∀ i ∈ S, z i = z' i) (C : ℝ) (hC : 1 ≤ C)
    (hz : ∀ i, |z i| ≤ 1) (hz' : ∀ i, |z' i| ≤ 1)
    (hNz : ∀ i, |N * z i| ≤ C) (hNz' : ∀ i, |N * z' i| ≤ C)
    (hNκ : ∀ i, |N * κ i| ≤ C) (a : Degree V 1) :
    |(∏ i, (if i ∈ S then N else 1) * propensitySlotFactor S κ z a i) -
      ∏ i, (if i ∈ S then N else 1) * propensitySlotFactor S κ z' a i| ≤
        C ^ Fintype.card V * ∑ i, |z i - z' i| := by
  have hf (i : V) :
      |(if i ∈ S then N else 1) * propensitySlotFactor S κ z a i -
        (if i ∈ S then N else 1) * propensitySlotFactor S κ z' a i| ≤ |z i - z' i| := by
    by_cases hi : i ∈ S
    · simp only [propensitySlotFactor, if_pos hi, hS i hi, sub_self, abs_zero, le_refl]
    · simp only [propensitySlotFactor, if_neg hi, one_mul]
      exact (Representative.abs_pow_sub_pow_le_unit _ _ (hz i) (hz' i) (a i).val).trans
        (by have ha : ((a i).val : ℝ) ≤ 1 := by exact_mod_cast Nat.le_of_lt_succ (a i).isLt
            simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (abs_nonneg (z i - z' i)))
  exact (abs_prod_sub_prod_le_bounded Finset.univ _ _ C hC
    (fun i _ => weightedPropensitySlotFactor_bound N κ z S C hC hz hNz hNκ a i)
    (fun i _ => weightedPropensitySlotFactor_bound N κ z' S C hC hz' hNz' hNκ a i)).trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hf i)) (pow_nonneg (by linarith) _))

theorem weightedPropensityPatternWeight_variable_sub_bound (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 1) (u : V × d → ℝ) (z z' : V → ℝ) (ζ : J → Bool)
    (S : Finset V) (hS : ∀ i ∈ S, z i = z' i) (C : ℝ) (hC : 1 ≤ C)
    (hz : ∀ i, |z i| ≤ 1) (hz' : ∀ i, |z' i| ≤ 1)
    (hNz : ∀ i, |N * z i| ≤ C) (hNz' : ∀ i, |N * z' i| ≤ C)
    (hNκ : ∀ i, |N * κ i| ≤ C) :
    |weightedPropensityPatternWeight N κ W u z ζ S -
      weightedPropensityPatternWeight N κ W u z' ζ S| ≤
        C ^ Fintype.card V * ‖W‖ * ∑ i, |z i - z' i| := by
  let b := C ^ Fintype.card V * ∑ i, |z i - z' i|
  have hb : 0 ≤ b := mul_nonneg (pow_nonneg (by linarith) _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  rw [weightedPropensityPatternWeight_expansion, weightedPropensityPatternWeight_expansion,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r : Row V J 1, |Walsh.character r.2 ζ * (toContinuous (W r) (torusProjection u)).re *
      ((∏ i, (if i ∈ S then N else 1) * propensitySlotFactor S κ z r.1 i) -
        ∏ i, (if i ∈ S then N else 1) * propensitySlotFactor S κ z' r.1 i)| := by
      simp only [mul_sub]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Row V J 1, ‖W r‖ * b := by
      apply Finset.sum_le_sum
      intro r _
      simp only [abs_mul, Walsh.abs_character, one_mul]
      exact mul_le_mul ((Complex.abs_re_le_norm _).trans (evaluate_bound _ _))
        (weightedPropensitySlotProduct_sub_bound N κ z z' S hS C hC hz hz' hNz hNz' hNκ r.1)
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, ← norm_eq_sum]; dsimp only [b]; ring

@[simp] theorem propensityPatternWeight_unit (κ : V → ℝ) (u : V × d → ℝ)
    (z : V → ℝ) (ζ : J → Bool) (S : Finset V) :
    propensityPatternWeight κ (unit : Array d V J 1) u z ζ S = ∏ i ∈ S, z i := by
  unfold propensityPatternWeight unit
  rw [Finset.sum_eq_single zeroRow]
  · rw [lp.single_apply_self]
    simp [zeroRow, propensitySlotFactor, Wiener.toContinuous_one]
  · intro r _ hr
    rw [lp.single_apply_ne _ _ _ hr, map_zero]
    simp
  · simp

theorem weightedPropensityPatternWeight_variable_sub_bound_centered (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 1) (u : V × d → ℝ) (z z' : V → ℝ) (ζ : J → Bool)
    (S : Finset V) (hS : ∀ i ∈ S, z i = z' i) (C : ℝ) (hC : 1 ≤ C)
    (hz : ∀ i, |z i| ≤ 1) (hz' : ∀ i, |z' i| ≤ 1)
    (hNz : ∀ i, |N * z i| ≤ C) (hNz' : ∀ i, |N * z' i| ≤ C)
    (hNκ : ∀ i, |N * κ i| ≤ C) :
    |weightedPropensityPatternWeight N κ W u z ζ S -
      weightedPropensityPatternWeight N κ W u z' ζ S| ≤
        C ^ Fintype.card V * ‖W - unit‖ * ∑ i, |z i - z' i| := by
  have hu : weightedPropensityPatternWeight N κ (unit : Array d V J 1) u z ζ S =
      weightedPropensityPatternWeight N κ unit u z' ζ S := by
    simp only [weightedPropensityPatternWeight, propensityPatternWeight_unit]
    rw [Finset.prod_congr rfl hS]
  have hb := weightedPropensityPatternWeight_variable_sub_bound N κ (W - unit) u z z' ζ S hS C hC
    hz hz' hNz hNz' hNκ
  rw [weightedPropensityPatternWeight_sub, weightedPropensityPatternWeight_sub, hu] at hb
  simpa only [sub_sub_sub_cancel_right] using hb

theorem weightedPropensityPatternWeight_remove_congr (T : Finset J) (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 1) (u : V × d → ℝ) (z : V → ℝ) (ζ ζ' : J → Bool)
    (he : ∀ j ∉ T, ζ j = ζ' j) (S : Finset V) :
    weightedPropensityPatternWeight N κ (remove T W) u z ζ S =
      weightedPropensityPatternWeight N κ (remove T W) u z ζ' S := by
  simp only [weightedPropensityPatternWeight, propensityPatternWeight]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [removed_row_coefficient_congr T W (torusProjection u) r ζ ζ' he]

theorem weightedPropensityPatternWeight_remove_error (T : Finset J) (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 1) (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (S : Finset V)
    (C : ℝ) (hC : 1 ≤ C) (hz : ∀ i, |z i| ≤ 1)
    (hNz : ∀ i, |N * z i| ≤ C) (hNκ : ∀ i, |N * κ i| ≤ C) :
    |weightedPropensityPatternWeight N κ W u z ζ S -
      weightedPropensityPatternWeight N κ (remove T W) u z ζ S| ≤
        C ^ Fintype.card V * ∑ j ∈ T, ‖symbolPart j W‖ := by
  rw [← weightedPropensityPatternWeight_sub]
  exact (weightedPropensityPatternWeight_bound N κ (W - remove T W) u z ζ S C hC hz hNz hNκ).trans
    (mul_le_mul_of_nonneg_left (removal_error T W) (pow_nonneg (by linarith) _))

theorem weightedPropensityPatternWeight_sign_sub_bound (T : Finset J) (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 1) (u : V × d → ℝ) (z : V → ℝ) (ζ ζ' : J → Bool)
    (he : ∀ j ∉ T, ζ j = ζ' j) (S : Finset V) (C : ℝ) (hC : 1 ≤ C)
    (hz : ∀ i, |z i| ≤ 1) (hNz : ∀ i, |N * z i| ≤ C) (hNκ : ∀ i, |N * κ i| ≤ C) :
    |weightedPropensityPatternWeight N κ W u z ζ S -
      weightedPropensityPatternWeight N κ W u z ζ' S| ≤
        C ^ Fintype.card V * (2 * ∑ j ∈ T, ‖symbolPart j W‖) := by
  have hr := weightedPropensityPatternWeight_remove_congr T N κ W u z ζ ζ' he S
  calc
    _ ≤ |weightedPropensityPatternWeight N κ W u z ζ S -
        weightedPropensityPatternWeight N κ (remove T W) u z ζ S| +
      |weightedPropensityPatternWeight N κ (remove T W) u z ζ S -
        weightedPropensityPatternWeight N κ W u z ζ' S| := abs_sub_le _ _ _
    _ ≤ (C ^ Fintype.card V * ∑ j ∈ T, ‖symbolPart j W‖) +
        C ^ Fintype.card V * ∑ j ∈ T, ‖symbolPart j W‖ := by
      apply add_le_add (weightedPropensityPatternWeight_remove_error T N κ W u z ζ S C hC hz hNz hNκ)
      rw [hr, abs_sub_comm]
      exact weightedPropensityPatternWeight_remove_error T N κ W u z ζ' S C hC hz hNz hNκ
    _ = _ := by ring

theorem weightedPropensityPatternWeight_resample_sub_bound (T : Finset J) (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 1) (u : V × d → ℝ) (z z' : V → ℝ) (ζ ζ' : J → Bool)
    (he : ∀ j ∉ T, ζ j = ζ' j) (S : Finset V) (hS : ∀ i ∈ S, z i = z' i)
    (C : ℝ) (hC : 1 ≤ C) (hz : ∀ i, |z i| ≤ 1) (hz' : ∀ i, |z' i| ≤ 1)
    (hNz : ∀ i, |N * z i| ≤ C) (hNz' : ∀ i, |N * z' i| ≤ C) (hNκ : ∀ i, |N * κ i| ≤ C) :
    |weightedPropensityPatternWeight N κ W u z ζ S -
      weightedPropensityPatternWeight N κ W u z' ζ' S| ≤
        C ^ Fintype.card V * (2 * (∑ j ∈ T, ‖symbolPart j W‖) +
          ‖W - unit‖ * ∑ i, |z i - z' i|) := by
  have hb := (abs_sub_le (weightedPropensityPatternWeight N κ W u z ζ S)
    (weightedPropensityPatternWeight N κ W u z ζ' S)
    (weightedPropensityPatternWeight N κ W u z' ζ' S)).trans
      (add_le_add (weightedPropensityPatternWeight_sign_sub_bound T N κ W u z ζ ζ' he S C hC hz hNz hNκ)
        (weightedPropensityPatternWeight_variable_sub_bound_centered N κ W u z z' ζ' S hS C hC
          hz hz' hNz hNz' hNκ))
  convert hb using 1 <;> ring

end CausalLowerbound.PartC

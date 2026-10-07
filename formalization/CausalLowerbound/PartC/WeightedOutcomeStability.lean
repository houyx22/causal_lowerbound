import CausalLowerbound.PartC.WeightedOutcomePatterns
import CausalLowerbound.PartC.RepresentativeStability

/-! Stability of normalized cubic pattern weights. Changes in ghost
variables cost the centered carrier norm, and changes in explicit Walsh
signs cost only the corresponding symbol parts. Selected values stay fixed. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative
variable {d V J : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

theorem weightedOutcomeSlotProduct_sub_bound (N : ℝ) (κ z z' : V → ℝ)
    (e : Degree V 3) (he : ∀ i, e i ≠ 0 → z i = z' i) (C : ℝ) (hC : 1 ≤ C)
    (hz : ∀ i, |z i| ≤ 1) (hz' : ∀ i, |z' i| ≤ 1)
    (hNz : ∀ i, |N * z i| ≤ C) (hNz' : ∀ i, |N * z' i| ≤ C)
    (hκ : ∀ i, |κ i| ≤ C) (a : Degree V 3) :
    |(∏ i, N ^ (e i).val * outcomeSlotFactor e κ z a i) -
      ∏ i, N ^ (e i).val * outcomeSlotFactor e κ z' a i| ≤
        (C ^ 4) ^ Fintype.card V * (3 * ∑ i, |z i - z' i|) := by
  have hf (i : V) :
      |N ^ (e i).val * outcomeSlotFactor e κ z a i -
        N ^ (e i).val * outcomeSlotFactor e κ z' a i| ≤ 3 * |z i - z' i| := by
    by_cases hi : e i = 0
    · simp only [outcomeSlotFactor, if_pos hi, hi, Fin.val_zero, pow_zero, one_mul]
      exact (Representative.abs_pow_sub_pow_le_unit _ _ (hz i) (hz' i) (a i).val).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt_succ (a i).isLt) (abs_nonneg _))
    · simp only [outcomeSlotFactor, if_neg hi, he i hi, sub_self, abs_zero]
      positivity
  have hb := (abs_prod_sub_prod_le_bounded Finset.univ _ _ (C ^ 4) (one_le_pow₀ hC)
    (fun i _ => weightedOutcomeSlotFactor_bound N e a κ z C hC hz hNz hκ i)
    (fun i _ => weightedOutcomeSlotFactor_bound N e a κ z' C hC hz' hNz' hκ i)).trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hf i)) (pow_nonneg (pow_nonneg (by linarith) _) _))
  simpa only [Finset.mul_sum] using hb

theorem weightedOutcomePatternWeight_variable_sub_bound (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 3) (u : V × d → ℝ) (z z' : V → ℝ) (ζ : J → Bool)
    (e : Degree V 3) (he : ∀ i, e i ≠ 0 → z i = z' i) (C : ℝ) (hC : 1 ≤ C)
    (hz : ∀ i, |z i| ≤ 1) (hz' : ∀ i, |z' i| ≤ 1)
    (hNz : ∀ i, |N * z i| ≤ C) (hNz' : ∀ i, |N * z' i| ≤ C) (hκ : ∀ i, |κ i| ≤ C) :
    |weightedOutcomePatternWeight N κ W u z ζ e - weightedOutcomePatternWeight N κ W u z' ζ e| ≤
      (C ^ 4) ^ Fintype.card V * ‖W‖ * (3 * ∑ i, |z i - z' i|) := by
  let b := (C ^ 4) ^ Fintype.card V * (3 * ∑ i, |z i - z' i|)
  rw [weightedOutcomePatternWeight_expansion, weightedOutcomePatternWeight_expansion, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r : Row V J 3, |Walsh.character r.2 ζ * (toContinuous (W r) (torusProjection u)).re *
      ((∏ i, N ^ (e i).val * outcomeSlotFactor e κ z r.1 i) -
        ∏ i, N ^ (e i).val * outcomeSlotFactor e κ z' r.1 i)| := by
      simp only [mul_sub]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Row V J 3, ‖W r‖ * b := by
      apply Finset.sum_le_sum
      intro r _
      simp only [abs_mul, Walsh.abs_character, one_mul]
      exact mul_le_mul ((Complex.abs_re_le_norm _).trans (evaluate_bound _ _))
        (weightedOutcomeSlotProduct_sub_bound N κ z z' e he C hC hz hz' hNz hNz' hκ r.1)
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, ← norm_eq_sum]; dsimp only [b]; ring

@[simp] theorem outcomePatternWeight_unit (κ : V → ℝ) (u : V × d → ℝ)
    (z : V → ℝ) (ζ : J → Bool) (e : Degree V 3) :
    outcomePatternWeight κ (unit : Array d V J 3) u z ζ e = ∏ i, z i ^ (e i).val := by
  have hs (i : V) : outcomeSlotFactor e κ z (fun _ => 0) i = z i ^ (e i).val := by
    by_cases hi : e i = 0 <;> simp [outcomeSlotFactor, outcomeMoment, hi]
  unfold outcomePatternWeight unit
  rw [Finset.sum_eq_single zeroRow]
  · rw [lp.single_apply_self]
    simpa only [zeroRow, Pi.zero_apply, Walsh.character_empty, Wiener.toContinuous_one,
      ContinuousMap.one_apply, Complex.one_re, one_mul] using
      (Finset.prod_congr rfl (fun i _ => hs i))
  · intro r _ hr
    rw [lp.single_apply_ne _ _ _ hr, map_zero]
    simp
  · simp

theorem weightedOutcomePatternWeight_variable_sub_bound_centered (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 3) (u : V × d → ℝ) (z z' : V → ℝ) (ζ : J → Bool)
    (e : Degree V 3) (he : ∀ i, e i ≠ 0 → z i = z' i) (C : ℝ) (hC : 1 ≤ C)
    (hz : ∀ i, |z i| ≤ 1) (hz' : ∀ i, |z' i| ≤ 1)
    (hNz : ∀ i, |N * z i| ≤ C) (hNz' : ∀ i, |N * z' i| ≤ C) (hκ : ∀ i, |κ i| ≤ C) :
    |weightedOutcomePatternWeight N κ W u z ζ e - weightedOutcomePatternWeight N κ W u z' ζ e| ≤
      (C ^ 4) ^ Fintype.card V * ‖W - unit‖ * (3 * ∑ i, |z i - z' i|) := by
  have hu : weightedOutcomePatternWeight N κ (unit : Array d V J 3) u z ζ e =
      weightedOutcomePatternWeight N κ unit u z' ζ e := by
    simp only [weightedOutcomePatternWeight, outcomePatternWeight_unit]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : e i = 0
    · simp only [hi, Fin.val_zero, pow_zero]
    · rw [he i hi]
  have hb := weightedOutcomePatternWeight_variable_sub_bound N κ (W - unit) u z z' ζ e he C hC
    hz hz' hNz hNz' hκ
  rw [weightedOutcomePatternWeight_sub, weightedOutcomePatternWeight_sub, hu] at hb
  simpa only [sub_sub_sub_cancel_right] using hb

theorem weightedOutcomePatternWeight_remove_congr (T : Finset J) (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 3) (u : V × d → ℝ) (z : V → ℝ) (ζ ζ' : J → Bool)
    (he : ∀ j ∉ T, ζ j = ζ' j) (e : Degree V 3) :
    weightedOutcomePatternWeight N κ (remove T W) u z ζ e =
      weightedOutcomePatternWeight N κ (remove T W) u z ζ' e := by
  simp only [weightedOutcomePatternWeight, outcomePatternWeight]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [removed_row_coefficient_congr T W (torusProjection u) r ζ ζ' he]

theorem weightedOutcomePatternWeight_remove_error (T : Finset J) (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 3) (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (e : Degree V 3)
    (C : ℝ) (hC : 1 ≤ C) (hz : ∀ i, |z i| ≤ 1) (hNz : ∀ i, |N * z i| ≤ C) (hκ : ∀ i, |κ i| ≤ C) :
    |weightedOutcomePatternWeight N κ W u z ζ e - weightedOutcomePatternWeight N κ (remove T W) u z ζ e| ≤
      (C ^ 4) ^ Fintype.card V * ∑ j ∈ T, ‖symbolPart j W‖ := by
  rw [← weightedOutcomePatternWeight_sub]
  exact (weightedOutcomePatternWeight_bound N κ (W - remove T W) u z ζ e C hC hz hNz hκ).trans
    (mul_le_mul_of_nonneg_left (removal_error T W) (pow_nonneg (pow_nonneg (by linarith) _) _))

theorem weightedOutcomePatternWeight_sign_sub_bound (T : Finset J) (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 3) (u : V × d → ℝ) (z : V → ℝ) (ζ ζ' : J → Bool)
    (he : ∀ j ∉ T, ζ j = ζ' j) (e : Degree V 3) (C : ℝ) (hC : 1 ≤ C)
    (hz : ∀ i, |z i| ≤ 1) (hNz : ∀ i, |N * z i| ≤ C) (hκ : ∀ i, |κ i| ≤ C) :
    |weightedOutcomePatternWeight N κ W u z ζ e - weightedOutcomePatternWeight N κ W u z ζ' e| ≤
      (C ^ 4) ^ Fintype.card V * (2 * ∑ j ∈ T, ‖symbolPart j W‖) := by
  have hr := weightedOutcomePatternWeight_remove_congr T N κ W u z ζ ζ' he e
  calc
    _ ≤ |weightedOutcomePatternWeight N κ W u z ζ e - weightedOutcomePatternWeight N κ (remove T W) u z ζ e| +
      |weightedOutcomePatternWeight N κ (remove T W) u z ζ e - weightedOutcomePatternWeight N κ W u z ζ' e| :=
        abs_sub_le _ _ _
    _ ≤ ((C ^ 4) ^ Fintype.card V * ∑ j ∈ T, ‖symbolPart j W‖) +
      (C ^ 4) ^ Fintype.card V * ∑ j ∈ T, ‖symbolPart j W‖ := by
      apply add_le_add (weightedOutcomePatternWeight_remove_error T N κ W u z ζ e C hC hz hNz hκ)
      rw [hr, abs_sub_comm]
      exact weightedOutcomePatternWeight_remove_error T N κ W u z ζ' e C hC hz hNz hκ
    _ = _ := by ring

theorem weightedOutcomePatternWeight_resample_sub_bound (T : Finset J) (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 3) (u : V × d → ℝ) (z z' : V → ℝ) (ζ ζ' : J → Bool)
    (hζ : ∀ j ∉ T, ζ j = ζ' j) (e : Degree V 3) (he : ∀ i, e i ≠ 0 → z i = z' i)
    (C : ℝ) (hC : 1 ≤ C) (hz : ∀ i, |z i| ≤ 1) (hz' : ∀ i, |z' i| ≤ 1)
    (hNz : ∀ i, |N * z i| ≤ C) (hNz' : ∀ i, |N * z' i| ≤ C) (hκ : ∀ i, |κ i| ≤ C) :
    |weightedOutcomePatternWeight N κ W u z ζ e - weightedOutcomePatternWeight N κ W u z' ζ' e| ≤
      (C ^ 4) ^ Fintype.card V * (2 * (∑ j ∈ T, ‖symbolPart j W‖) +
        ‖W - unit‖ * (3 * ∑ i, |z i - z' i|)) := by
  have hb := (abs_sub_le (weightedOutcomePatternWeight N κ W u z ζ e)
    (weightedOutcomePatternWeight N κ W u z ζ' e)
    (weightedOutcomePatternWeight N κ W u z' ζ' e)).trans
      (add_le_add (weightedOutcomePatternWeight_sign_sub_bound T N κ W u z ζ ζ' hζ e C hC hz hNz hκ)
        (weightedOutcomePatternWeight_variable_sub_bound_centered N κ W u z z' ζ' e he C hC
          hz hz' hNz hNz' hκ))
  convert hb using 1 <;> ring

end CausalLowerbound.PartC

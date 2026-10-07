import CausalLowerbound.PartC.OutcomePatternParity

/-! Absorb the normalization into the selected cubic output powers.
The resulting bounds depend on N*z and the variance bound, and have no
remaining positive power of N. This preserves the physical shift a*t. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative
variable {d V J : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

def weightedOutcomePatternWeight (N : ℝ) (κ : V → ℝ) (W : Array d V J 3)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (e : Degree V 3) : ℝ :=
  N ^ degreeSize e * outcomePatternWeight κ W u z ζ e

theorem weightedOutcomePatternWeight_amplitude (amp N : ℝ) (κ : V → ℝ) (W : Array d V J 3)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (e : Degree V 3) :
    (amp * N) ^ degreeSize e * outcomePatternWeight κ W u z ζ e =
      amp ^ degreeSize e * weightedOutcomePatternWeight N κ W u z ζ e := by
  simp only [weightedOutcomePatternWeight, mul_pow, mul_assoc]

theorem weightedOutcomeSlotFactor_selected (N : ℝ) (e a : Degree V 3) (κ z : V → ℝ)
    (i : V) (hi : e i ≠ 0) :
    N ^ (e i).val * outcomeSlotFactor e κ z a i =
      outcomeMoment (κ i) (a i) * (N * z i) ^ (e i).val := by
  rw [outcomeSlotFactor, if_neg hi, mul_pow]
  ring

theorem weightedOutcomeSlotFactor_bound (N : ℝ) (e a : Degree V 3) (κ z : V → ℝ)
    (C : ℝ) (hC : 1 ≤ C) (hz : ∀ i, |z i| ≤ 1) (hNz : ∀ i, |N * z i| ≤ C)
    (hκ : ∀ i, |κ i| ≤ C) (i : V) :
    |N ^ (e i).val * outcomeSlotFactor e κ z a i| ≤ C ^ 4 := by
  by_cases hi : e i = 0
  · simp only [outcomeSlotFactor, if_pos hi, hi, if_true, Fin.val_zero, pow_zero, one_mul, abs_pow]
    exact (pow_le_one₀ (abs_nonneg _) (hz i)).trans (one_le_pow₀ hC)
  · rw [weightedOutcomeSlotFactor_selected N e a κ z i hi, abs_mul, abs_pow]
    have hp : |N * z i| ^ (e i).val ≤ C ^ 3 :=
      (pow_le_pow_left₀ (abs_nonneg _) (hNz i) _).trans
        (pow_le_pow_right₀ hC (Nat.le_of_lt_succ (e i).isLt))
    calc
      _ ≤ C * C ^ 3 := mul_le_mul (outcomeMoment_abs_le _ C hC (hκ i) _) hp
        (pow_nonneg (abs_nonneg _) _) (zero_le_one.trans hC)
      _ = _ := by ring

theorem weightedOutcomePatternWeight_expansion (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 3) (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (e : Degree V 3) :
    weightedOutcomePatternWeight N κ W u z ζ e =
      ∑ r : Row V J 3, Walsh.character r.2 ζ * (toContinuous (W r) (torusProjection u)).re *
        ∏ i, N ^ (e i).val * outcomeSlotFactor e κ z r.1 i := by
  have hp (a : Degree V 3) :
      N ^ degreeSize e * (∏ i, outcomeSlotFactor e κ z a i) =
        ∏ i, N ^ (e i).val * outcomeSlotFactor e κ z a i := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rfl
  simp only [weightedOutcomePatternWeight, outcomePatternWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [← hp]
  ring

theorem weightedOutcomePatternWeight_bound (N : ℝ) (κ : V → ℝ) (W : Array d V J 3)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (e : Degree V 3)
    (C : ℝ) (hC : 1 ≤ C) (hz : ∀ i, |z i| ≤ 1)
    (hNz : ∀ i, |N * z i| ≤ C) (hκ : ∀ i, |κ i| ≤ C) :
    |weightedOutcomePatternWeight N κ W u z ζ e| ≤ (C ^ 4) ^ Fintype.card V * ‖W‖ := by
  have hp (a : Degree V 3) : |∏ i, N ^ (e i).val * outcomeSlotFactor e κ z a i| ≤
      (C ^ 4) ^ Fintype.card V := by
    rw [Finset.abs_prod]
    have hb := Finset.prod_le_prod (s := Finset.univ) (fun _ _ => abs_nonneg _)
      (fun i _ => weightedOutcomeSlotFactor_bound N e a κ z C hC hz hNz hκ i)
    simpa only [Finset.prod_const, Finset.card_univ] using hb
  rw [weightedOutcomePatternWeight_expansion]
  calc
    _ ≤ ∑ r : Row V J 3, |Walsh.character r.2 ζ * (toContinuous (W r) (torusProjection u)).re *
        ∏ i, N ^ (e i).val * outcomeSlotFactor e κ z r.1 i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Row V J 3, ‖W r‖ * (C ^ 4) ^ Fintype.card V := by
      apply Finset.sum_le_sum
      intro r _
      simp only [abs_mul, Walsh.abs_character, one_mul]
      exact mul_le_mul ((Complex.abs_re_le_norm _).trans (Wiener.evaluate_bound _ _)) (hp r.1)
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, ← norm_eq_sum]; ring

theorem weightedOutcomePatternWeight_sub (N : ℝ) (κ : V → ℝ) (W B : Array d V J 3)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (e : Degree V 3) :
    weightedOutcomePatternWeight N κ (W - B) u z ζ e =
      weightedOutcomePatternWeight N κ W u z ζ e - weightedOutcomePatternWeight N κ B u z ζ e := by
  simp only [weightedOutcomePatternWeight, outcomePatternWeight_sub, mul_sub]

theorem weightedOutcomePatternWeight_reflection_fixed (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 3) (hW : reflection W = W) (u : V × d → ℝ)
    (z : (J → Bool) → V → ℝ) (hz : ∀ ζ i, z (Walsh.flip ζ) i = -z ζ i)
    (ζ : J → Bool) (e : Degree V 3) :
    weightedOutcomePatternWeight N κ W u (z (Walsh.flip ζ)) (Walsh.flip ζ) e =
      (-1) ^ degreeSize e * weightedOutcomePatternWeight N κ W u (z ζ) ζ e := by
  simp only [weightedOutcomePatternWeight, outcomePatternWeight_reflection_fixed κ W hW u z hz]
  ring

end CausalLowerbound.PartC

import CausalLowerbound.PartC.PropensityPatternParity

/-! Moving the carrier normalization into each selected slot. The
resulting weight has a bound independent of the normalization whenever
N z and N κ are bounded; it has the same parity and remains linear in
the representative. This keeps the physical shift amplitude available. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative
variable {d V J : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

def weightedPropensityPatternWeight (N : ℝ) (κ : V → ℝ) (W : Array d V J 1)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (S : Finset V) : ℝ :=
  N ^ S.card * propensityPatternWeight κ W u z ζ S

theorem weightedPropensityPatternWeight_amplitude (amp N : ℝ) (κ : V → ℝ) (W : Array d V J 1)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (S : Finset V) :
    (amp * N) ^ S.card * propensityPatternWeight κ W u z ζ S =
      amp ^ S.card * weightedPropensityPatternWeight N κ W u z ζ S := by
  simp only [weightedPropensityPatternWeight, mul_pow, mul_assoc]

theorem weightedPropensityPatternWeight_bound (N : ℝ) (κ : V → ℝ) (W : Array d V J 1)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (S : Finset V)
    (C : ℝ) (hC : 1 ≤ C) (hz : ∀ i, |z i| ≤ 1)
    (hNz : ∀ i, |N * z i| ≤ C) (hNκ : ∀ i, |N * κ i| ≤ C) :
    |weightedPropensityPatternWeight N κ W u z ζ S| ≤ C ^ Fintype.card V * ‖W‖ := by
  have hprod (a : Degree V 1) :
      N ^ S.card * (∏ i, propensitySlotFactor S κ z a i) =
        ∏ i, (if i ∈ S then N else 1) * propensitySlotFactor S κ z a i := by
    rw [Finset.prod_mul_distrib]
    simp
  have hb (a : Degree V 1) :
      |∏ i, (if i ∈ S then N else 1) * propensitySlotFactor S κ z a i| ≤ C ^ Fintype.card V := by
    rw [Finset.abs_prod]
    have hh : (∏ i, |(if i ∈ S then N else 1) * propensitySlotFactor S κ z a i|) ≤ ∏ _i : V, C := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro i _
      by_cases hi : i ∈ S
      · by_cases ha : a i = 0
        · simpa only [propensitySlotFactor, if_pos hi, if_pos ha] using hNz i
        · simpa only [propensitySlotFactor, if_pos hi, if_neg ha] using hNκ i
      · simp only [if_neg hi, propensitySlotFactor, one_mul, abs_pow]
        exact (pow_le_one₀ (abs_nonneg _) (hz i)).trans hC
    simpa using hh
  have hvalue : weightedPropensityPatternWeight N κ W u z ζ S =
      ∑ r : Row V J 1, Walsh.character r.2 ζ * (toContinuous (W r) (torusProjection u)).re *
        ∏ i, (if i ∈ S then N else 1) * propensitySlotFactor S κ z r.1 i := by
    simp only [weightedPropensityPatternWeight, propensityPatternWeight, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [← hprod]
    ring
  rw [hvalue]
  calc
    _ ≤ ∑ r : Row V J 1, |Walsh.character r.2 ζ * (toContinuous (W r) (torusProjection u)).re *
        ∏ i, (if i ∈ S then N else 1) * propensitySlotFactor S κ z r.1 i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Row V J 1, ‖W r‖ * C ^ Fintype.card V := by
      apply Finset.sum_le_sum
      intro r _
      simp only [abs_mul, Walsh.abs_character, one_mul]
      exact mul_le_mul ((Complex.abs_re_le_norm _).trans (Wiener.evaluate_bound _ _)) (hb r.1)
        (abs_nonneg _) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, ← norm_eq_sum]; ring

theorem weightedPropensityPatternWeight_sub (N : ℝ) (κ : V → ℝ) (W B : Array d V J 1)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (S : Finset V) :
    weightedPropensityPatternWeight N κ (W - B) u z ζ S =
      weightedPropensityPatternWeight N κ W u z ζ S - weightedPropensityPatternWeight N κ B u z ζ S := by
  simp only [weightedPropensityPatternWeight, propensityPatternWeight_sub, mul_sub]

theorem weightedPropensityPatternWeight_reflection_fixed (N : ℝ) (κ : V → ℝ)
    (W : Array d V J 1) (hW : reflection W = W) (u : V × d → ℝ)
    (z : (J → Bool) → V → ℝ) (hz : ∀ ζ i, z (Walsh.flip ζ) i = -z ζ i)
    (ζ : J → Bool) (S : Finset V) :
    weightedPropensityPatternWeight N κ W u (z (Walsh.flip ζ)) (Walsh.flip ζ) S =
      (-1) ^ S.card * weightedPropensityPatternWeight N κ W u (z ζ) ζ S := by
  simp only [weightedPropensityPatternWeight, propensityPatternWeight_reflection_fixed κ W hW u z hz]
  ring

end CausalLowerbound.PartC

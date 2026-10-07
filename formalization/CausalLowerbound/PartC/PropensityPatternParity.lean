import CausalLowerbound.PartC.PropensityPolynomialTarget
import CausalLowerbound.PartC.RepresentativeReflection

/-! The actual degree-one design substitution has parity equal to the
number of selected slots, and is a contraction at bounded real slot
values and corrections. Both facts concern the existing target weights. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative
variable {d V J : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

theorem propensitySlotFactor_neg (S : Finset V) (κ z : V → ℝ) (a : Degree V 1) (i : V) :
    propensitySlotFactor S κ (fun j => -z j) a i =
      (-1) ^ ((a i).val + if i ∈ S then 1 else 0) * propensitySlotFactor S κ z a i := by
  by_cases hi : i ∈ S
  · by_cases ha : a i = 0
    · simp [propensitySlotFactor, hi, ha]
    · have ha1 : a i = 1 := by
        apply Fin.ext
        change (a i).val = 1
        have hlt : (a i).val < 2 := (a i).isLt
        have hn : (a i).val ≠ 0 := by intro hz; exact ha (Fin.ext hz)
        omega
      simp [propensitySlotFactor, hi, ha1]
  · simpa only [propensitySlotFactor, if_neg hi, add_zero] using neg_pow (z i) (a i).val

theorem propensitySlotFactor_product_neg (S : Finset V) (κ z : V → ℝ) (a : Degree V 1) :
    (∏ i, propensitySlotFactor S κ (fun j => -z j) a i) =
      (-1) ^ (degreeSize a + S.card) * ∏ i, propensitySlotFactor S κ z a i := by
  simp only [propensitySlotFactor_neg, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_add_distrib]
  congr 2
  simp only [degreeSize]
  simp

theorem propensitySlotFactor_bound (S : Finset V) (κ z : V → ℝ)
    (hκ : ∀ i, |κ i| ≤ 1) (hz : ∀ i, |z i| ≤ 1) (a : Degree V 1) (i : V) :
    |propensitySlotFactor S κ z a i| ≤ 1 := by
  unfold propensitySlotFactor
  split_ifs
  · exact hz i
  · exact hκ i
  · rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hz i)

theorem propensityPatternWeight_bound (κ : V → ℝ) (W : Array d V J 1) (u : V × d → ℝ)
    (z : V → ℝ) (ζ : J → Bool) (S : Finset V)
    (hκ : ∀ i, |κ i| ≤ 1) (hz : ∀ i, |z i| ≤ 1) :
    |propensityPatternWeight κ W u z ζ S| ≤ ‖W‖ := by
  calc
    _ ≤ ∑ r : Row V J 1, |Walsh.character r.2 ζ * (toContinuous (W r) (torusProjection u)).re *
        ∏ i, propensitySlotFactor S κ z r.1 i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Row V J 1, ‖W r‖ := by
      apply Finset.sum_le_sum
      intro r _
      simp only [abs_mul, Walsh.abs_character, one_mul]
      have hp : |∏ i, propensitySlotFactor S κ z r.1 i| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
          (fun i _ => propensitySlotFactor_bound S κ z hκ hz r.1 i)
      exact (mul_le_mul ((Complex.abs_re_le_norm _).trans (Wiener.evaluate_bound _ _)) hp
        (abs_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
    _ = _ := (norm_eq_sum W).symm

theorem propensityPatternWeight_flip (κ : V → ℝ) (W : Array d V J 1) (u : V × d → ℝ)
    (z : V → ℝ) (ζ : J → Bool) (S : Finset V) :
    propensityPatternWeight κ W u (fun i => -z i) (Walsh.flip ζ) S =
      (-1) ^ S.card * propensityPatternWeight κ (reflection W) u z ζ S := by
  simp only [propensityPatternWeight, Walsh.character_flip, propensitySlotFactor_product_neg,
    reflection_apply, Wiener.toContinuous_real_smul, ContinuousMap.smul_apply, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    rowSign, pow_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem propensityPatternWeight_reflection_fixed (κ : V → ℝ) (W : Array d V J 1)
    (hW : reflection W = W) (u : V × d → ℝ) (z : (J → Bool) → V → ℝ)
    (hz : ∀ ζ i, z (Walsh.flip ζ) i = -z ζ i) (ζ : J → Bool) (S : Finset V) :
    propensityPatternWeight κ W u (z (Walsh.flip ζ)) (Walsh.flip ζ) S =
      (-1) ^ S.card * propensityPatternWeight κ W u (z ζ) ζ S := by
  have he : z (Walsh.flip ζ) = fun i => -z ζ i := funext (hz ζ)
  rw [he, propensityPatternWeight_flip, hW]

theorem propensityPatternWeight_sub (κ : V → ℝ) (W B : Array d V J 1) (u : V × d → ℝ)
    (z : V → ℝ) (ζ : J → Bool) (S : Finset V) :
    propensityPatternWeight κ (W - B) u z ζ S =
      propensityPatternWeight κ W u z ζ S - propensityPatternWeight κ B u z ζ S := by
  simp only [propensityPatternWeight, lp.coeFn_sub, Pi.sub_apply, map_sub,
    ContinuousMap.sub_apply, Complex.sub_re, mul_sub, sub_mul, Finset.sum_sub_distrib]

end CausalLowerbound.PartC

import CausalLowerbound.PartC.OutcomePolynomialTarget
import CausalLowerbound.PartC.RepresentativeReflection

/-! The cubic design substitution has the parity of its total output
degree. Odd input moments vanish exactly, so reflection of the carrier
supplies the cancellation needed to retain the target amplitude. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative
variable {d V J : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

theorem outcomeMoment_sign (v : ℝ) (f : Fin 4) :
    (-1 : ℝ) ^ f.val * outcomeMoment v f = outcomeMoment v f := by
  fin_cases f <;> norm_num [outcomeMoment, Fin.ext_iff]

theorem outcomeMoment_abs_le (v C : ℝ) (hC : 1 ≤ C) (hv : |v| ≤ C) (f : Fin 4) :
    |outcomeMoment v f| ≤ C := by
  unfold outcomeMoment
  split_ifs
  · simpa only [abs_one] using hC
  · exact hv
  · simpa only [abs_zero] using zero_le_one.trans hC

theorem outcomeSlotFactor_neg (e : Degree V 3) (κ z : V → ℝ) (a : Degree V 3) (i : V) :
    outcomeSlotFactor e κ (fun j => -z j) a i =
      (-1) ^ ((a i).val + (e i).val) * outcomeSlotFactor e κ z a i := by
  by_cases he : e i = 0
  · simpa only [outcomeSlotFactor, if_pos he, he, Fin.val_zero, add_zero] using neg_pow (z i) (a i).val
  · simp only [outcomeSlotFactor, if_neg he]
    rw [neg_pow (z i), pow_add]
    have hs := congrArg (fun b : ℝ => (-1) ^ (e i).val * b * z i ^ (e i).val)
      (outcomeMoment_sign (κ i) (a i))
    calc
      _ = (-1) ^ (e i).val * outcomeMoment (κ i) (a i) * z i ^ (e i).val := by ring
      _ = (-1) ^ (e i).val * ((-1) ^ (a i).val * outcomeMoment (κ i) (a i)) * z i ^ (e i).val := hs.symm
      _ = _ := by ring

theorem outcomeSlotFactor_product_neg (e : Degree V 3) (κ z : V → ℝ) (a : Degree V 3) :
    (∏ i, outcomeSlotFactor e κ (fun j => -z j) a i) =
      (-1) ^ (degreeSize a + degreeSize e) * ∏ i, outcomeSlotFactor e κ z a i := by
  simp only [outcomeSlotFactor_neg, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.sum_add_distrib, degreeSize]

theorem outcomePatternWeight_flip (κ : V → ℝ) (W : Array d V J 3) (u : V × d → ℝ)
    (z : V → ℝ) (ζ : J → Bool) (e : Degree V 3) :
    outcomePatternWeight κ W u (fun i => -z i) (Walsh.flip ζ) e =
      (-1) ^ degreeSize e * outcomePatternWeight κ (reflection W) u z ζ e := by
  simp only [outcomePatternWeight, Walsh.character_flip, outcomeSlotFactor_product_neg,
    reflection_apply, Wiener.toContinuous_real_smul, ContinuousMap.smul_apply, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    rowSign, pow_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem outcomePatternWeight_reflection_fixed (κ : V → ℝ) (W : Array d V J 3)
    (hW : reflection W = W) (u : V × d → ℝ) (z : (J → Bool) → V → ℝ)
    (hz : ∀ ζ i, z (Walsh.flip ζ) i = -z ζ i) (ζ : J → Bool) (e : Degree V 3) :
    outcomePatternWeight κ W u (z (Walsh.flip ζ)) (Walsh.flip ζ) e =
      (-1) ^ degreeSize e * outcomePatternWeight κ W u (z ζ) ζ e := by
  have he : z (Walsh.flip ζ) = fun i => -z ζ i := funext (hz ζ)
  rw [he, outcomePatternWeight_flip, hW]

theorem outcomePatternWeight_sub (κ : V → ℝ) (W B : Array d V J 3) (u : V × d → ℝ)
    (z : V → ℝ) (ζ : J → Bool) (e : Degree V 3) :
    outcomePatternWeight κ (W - B) u z ζ e =
      outcomePatternWeight κ W u z ζ e - outcomePatternWeight κ B u z ζ e := by
  simp only [outcomePatternWeight, lp.coeFn_sub, Pi.sub_apply, map_sub,
    ContinuousMap.sub_apply, Complex.sub_re, mul_sub, sub_mul, Finset.sum_sub_distrib]

end CausalLowerbound.PartC

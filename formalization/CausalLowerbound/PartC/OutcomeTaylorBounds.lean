import CausalLowerbound.PartC.CubicTaylorEvaluation

/-! Each cubic Taylor coefficient has exactly its degree of the shift
amplitude, and its remaining coefficient is affine in the rough field.
Uniform bounds therefore retain one rough-amplitude factor in deviations
from the sign-independent baseline. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open RoughOutcome

def outcomeTaylorBase (R smooth : ℝ) (f : Fin 4) : ℝ :=
  if f = 0 then 1 + R * smooth else if f = 1 then R else 0

def outcomeTaylorSlope (R T η smooth : ℝ) (f : Fin 4) : ℝ :=
  if f = 0 then (1 + R * smooth) * T * (1 + η - smooth ^ 2)
  else if f = 1 then R * T * (1 + η) - 2 * T * smooth - 3 * R * T * smooth ^ 2
  else if f = 2 then -T * (1 + 3 * R * smooth)
  else -R * T

theorem outcomeTaylorCoefficient_scaled_affine (R T shift jb η smooth rough : ℝ) (f : Fin 4) :
    outcomeTaylorCoefficient R T shift jb η smooth rough f =
      shift ^ f.val * (outcomeTaylorBase R smooth f + (jb * rough) * outcomeTaylorSlope R T η smooth f) := by
  fin_cases f <;>
    simp [outcomeTaylorCoefficient, outcomeTaylorBase, outcomeTaylorSlope,
      likelihood, outcome, incrementOne, incrementTwo, incrementThree] <;> ring <;> simp

theorem outcomeTaylorCoefficient_scale (R T shift jb η smooth rough : ℝ) (f : Fin 4) :
    outcomeTaylorCoefficient R T shift jb η smooth rough f =
      shift ^ f.val * outcomeTaylorCoefficient R T 1 jb η smooth rough f := by
  rw [outcomeTaylorCoefficient_scaled_affine, outcomeTaylorCoefficient_scaled_affine]
  simp only [one_pow, one_mul]

theorem outcomeTaylorBase_bound (R smooth : ℝ) (hR : |R| ≤ 1) (hs : |smooth| ≤ 1) (f : Fin 4) :
    |outcomeTaylorBase R smooth f| ≤ 2 := by
  have hrs : |R * smooth| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hR hs (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hb : |1 + R * smooth| ≤ 2 := by
    exact (abs_add _ _).trans (by rw [abs_one]; linarith)
  fin_cases f <;> simp only [outcomeTaylorBase, Fin.reduceEq, if_true, if_false, abs_zero]
  · exact hb
  · exact hR.trans (by norm_num)
  · norm_num
  · norm_num

theorem outcomeTaylorSlope_bound (R T η smooth : ℝ)
    (hR : |R| ≤ 1) (hT : |T| ≤ 1) (hη : |η| ≤ 3) (hs : |smooth| ≤ 1) (f : Fin 4) :
    |outcomeTaylorSlope R T η smooth f| ≤ 10 := by
  have hrs : |R * smooth| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hR hs (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hs2 : |smooth| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hs
  have hb : |1 + R * smooth| ≤ 2 :=
    (abs_add _ _).trans (by rw [abs_one]; linarith)
  have hη1 : |1 + η| ≤ 4 :=
    (abs_add _ _).trans (by rw [abs_one]; linarith)
  have hη2 : |1 + η - smooth ^ 2| ≤ 5 := by
    apply (abs_sub _ _).trans
    rw [abs_pow]
    linarith
  have hb3 : |1 + 3 * R * smooth| ≤ 4 := by
    calc
      _ ≤ |(1 : ℝ)| + |3 * R * smooth| := abs_add _ _
      _ = 1 + 3 * |R * smooth| := by simp only [abs_one, ← mul_assoc, abs_mul]; norm_num
      _ ≤ 4 := by linarith
  have h0 : |(1 + R * smooth) * T * (1 + η - smooth ^ 2)| ≤ 10 := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ 2 * 1 * 5 := mul_le_mul
        (mul_le_mul hb hT (abs_nonneg _) (by norm_num)) hη2 (abs_nonneg _) (by norm_num)
      _ = 10 := by norm_num
  have h1 : |R * T * (1 + η) - 2 * T * smooth - 3 * R * T * smooth ^ 2| ≤ 10 := by
    calc
      _ ≤ (|R * T * (1 + η)| + |2 * T * smooth|) + |3 * R * T * smooth ^ 2| :=
        (abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)
      _ = (|R| * |T| * |1 + η| + 2 * |T| * |smooth|) + 3 * |R| * |T| * |smooth| ^ 2 := by
        simp only [abs_mul, abs_pow]
        norm_num
      _ ≤ (1 * 1 * 4 + 2 * 1 * 1) + 3 * 1 * 1 * 1 := by gcongr
      _ ≤ 10 := by norm_num
  have h2 : |-T * (1 + 3 * R * smooth)| ≤ 10 := by
    rw [abs_mul, abs_neg]
    calc
      _ ≤ 1 * 4 := mul_le_mul hT hb3 (abs_nonneg _) (by norm_num)
      _ ≤ 10 := by norm_num
  have h3 : |-R * T| ≤ 10 := by
    rw [abs_mul, abs_neg]
    exact (mul_le_mul hR hT (abs_nonneg _) zero_le_one).trans (by norm_num)
  fin_cases f
  · simpa only [outcomeTaylorSlope, Fin.reduceEq, if_true, if_false] using h0
  · simpa only [outcomeTaylorSlope, Fin.reduceEq, if_true, if_false] using h1
  · simpa only [outcomeTaylorSlope, Fin.reduceEq, if_true, if_false] using h2
  · simpa only [outcomeTaylorSlope, Fin.reduceEq, if_true, if_false] using h3

theorem outcomeTaylorCoefficient_unit_bounds (R T jb η smooth rough ρ : ℝ)
    (hR : |R| ≤ 1) (hT : |T| ≤ 1) (hη : |η| ≤ 3) (hs : |smooth| ≤ 1)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hr : |jb * rough| ≤ ρ) (f : Fin 4) :
    |outcomeTaylorCoefficient R T 1 jb η smooth rough f| ≤ 12 ∧
      |outcomeTaylorCoefficient R T 1 jb η smooth rough f - outcomeTaylorBase R smooth f| ≤ 12 * ρ := by
  have hbase := outcomeTaylorBase_bound R smooth hR hs f
  have hslope := outcomeTaylorSlope_bound R T η smooth hR hT hη hs f
  have hd : |jb * rough * outcomeTaylorSlope R T η smooth f| ≤ 10 * ρ := by
    rw [abs_mul]
    exact (mul_le_mul hr hslope (abs_nonneg _) hρ).trans_eq (mul_comm _ _)
  rw [outcomeTaylorCoefficient_scaled_affine]
  simp only [one_pow, one_mul]
  constructor
  · exact (abs_add _ _).trans (by linarith)
  · rw [add_sub_cancel_left]
    exact hd.trans (by nlinarith)

end CausalLowerbound.PartC

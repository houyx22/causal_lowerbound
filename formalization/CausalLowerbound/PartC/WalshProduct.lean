import CausalLowerbound.PartC.WalshRemoval
import Mathlib.Data.Finset.SymmDiff

/-! Actual multiplication and powers of finite Walsh arrays. Repeated signs
are reduced by symmetric difference. The absolute coefficient norm is
submultiplicative and each symbol projection satisfies a derivation bound. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators symmDiff ENNReal

namespace CausalLowerbound.PartC.Walsh

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem character_symmDiff (S T : Finset J) (ζ : J → Bool) :
    character (S ∆ T) ζ = character S ζ * character T ζ := by
  simp only [character_eq_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;>
    simp [Finset.mem_symmDiff, hS, hT, ← sq, PartB.sign_sq]

def product (a b : Coefficients J) : Coefficients J :=
  ∑ S : Finset J, ∑ T : Finset J, lp.single 1 (S ∆ T) (a S * b T)

theorem product_norm (a b : Coefficients J) : ‖product a b‖ ≤ ‖a‖ * ‖b‖ := by
  calc
    _ ≤ ∑ S : Finset J, ‖∑ T : Finset J,
        (lp.single 1 (S ∆ T) (a S * b T) : Coefficients J)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ S : Finset J, ∑ T : Finset J,
        ‖(lp.single 1 (S ∆ T) (a S * b T) : Coefficients J)‖ :=
      Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ = _ := by
      simp only [lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞)), Real.norm_eq_abs, abs_mul,
        norm_eq_sum, Finset.sum_mul_sum]

theorem evaluate_product (ζ : J → Bool) (a b : Coefficients J) :
    evaluate ζ (product a b) = evaluate ζ a * evaluate ζ b := by
  simp only [product, map_sum]
  simp only [evaluate_single, character_symmDiff]
  simp only [evaluate_apply, tsum_fintype, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  ring

theorem symbolPart_norm (j : J) (a : Coefficients J) :
    ‖symbolPart j a‖ = ∑ S : Finset J, if j ∈ S then |a S| else 0 := by
  rw [norm_eq_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [symbolPart_apply]
  split_ifs <;> simp

theorem product_symbol_bound (j : J) (a b : Coefficients J) :
    ‖symbolPart j (product a b)‖ ≤
      ‖symbolPart j a‖ * ‖b‖ + ‖a‖ * ‖symbolPart j b‖ := by
  have hterm (S T : Finset J) :
      ‖symbolPart j (lp.single 1 (S ∆ T) (a S * b T))‖ ≤
        (if j ∈ S then |a S| else 0) * |b T| +
          |a S| * (if j ∈ T then |b T| else 0) := by
    by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;>
      simp [symbolPart, project_single, Finset.mem_symmDiff, hS, hT,
        lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞)), Real.norm_eq_abs, abs_mul] <;> positivity
  calc
    _ = ‖∑ S : Finset J, ∑ T : Finset J,
        symbolPart j (lp.single 1 (S ∆ T) (a S * b T))‖ := by
      simp only [product, map_sum]
    _ ≤ ∑ S : Finset J, ∑ T : Finset J,
        ‖symbolPart j (lp.single 1 (S ∆ T) (a S * b T))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ S : Finset J, ∑ T : Finset J,
        ((if j ∈ S then |a S| else 0) * |b T| +
          |a S| * (if j ∈ T then |b T| else 0)) :=
      Finset.sum_le_sum (fun S _ => Finset.sum_le_sum (fun T _ => hterm S T))
    _ = _ := by
      simp_rw [symbolPart_norm]
      simp only [norm_eq_sum, Finset.sum_mul_sum, Finset.sum_add_distrib]

def power (a : Coefficients J) : ℕ → Coefficients J
  | 0 => lp.single 1 ∅ 1
  | n + 1 => product a (power a n)

theorem evaluate_power (ζ : J → Bool) (a : Coefficients J) (n : ℕ) :
    evaluate ζ (power a n) = evaluate ζ a ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => rw [power, evaluate_product, ih, pow_succ, mul_comm]

theorem power_norm (a : Coefficients J) (n : ℕ) : ‖power a n‖ ≤ ‖a‖ ^ n := by
  induction n with
  | zero => simp [power, lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))]
  | succ n ih =>
    exact (product_norm a (power a n)).trans (by
      simpa only [pow_succ, mul_comm] using mul_le_mul_of_nonneg_left ih (norm_nonneg a))

theorem power_symbol_bound (j : J) (a : Coefficients J) (n : ℕ) :
    ‖symbolPart j (power a n)‖ ≤ (n : ℝ) * ‖a‖ ^ (n - 1) * ‖symbolPart j a‖ := by
  induction n with
  | zero => simp [power, symbolPart, project_single]
  | succ n ih =>
    calc
      _ ≤ ‖symbolPart j a‖ * ‖power a n‖ + ‖a‖ * ‖symbolPart j (power a n)‖ :=
        product_symbol_bound j a (power a n)
      _ ≤ ‖symbolPart j a‖ * ‖a‖ ^ n +
          ‖a‖ * ((n : ℝ) * ‖a‖ ^ (n - 1) * ‖symbolPart j a‖) :=
        add_le_add (mul_le_mul_of_nonneg_left (power_norm a n) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left ih (norm_nonneg a))
      _ = _ := by
        cases n <;> simp [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring

end CausalLowerbound.PartC.Walsh

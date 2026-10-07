import CausalLowerbound.PartC.CrossBlockRemoval

/-! Changing substituted rough variables costs the norm of B - 1,
not the norm of B. This preserves the small carrier increment when
ghost variables depend on signs being resampled at retained sites. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC.Representative
open Wiener
variable {d V J : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] {D : ℕ}

theorem abs_pow_sub_pow_le_unit (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (n : ℕ) :
    |x ^ n - y ^ n| ≤ n * |x - y| := by
  simpa only [Finset.prod_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] using abs_prod_sub_prod_le (Finset.univ : Finset (Fin n))
      (fun _ => x) (fun _ => y) (fun _ _ => hx) (fun _ _ => hy)

theorem monomial_sub_bound (e : Degree V D) (z z' : V → ℝ)
    (hz : ∀ i, |z i| ≤ 1) (hz' : ∀ i, |z' i| ≤ 1) :
    |monomial e z - monomial e z'| ≤ (D : ℝ) * ∑ i, |z i - z' i| := by
  apply (abs_prod_sub_prod_le Finset.univ _ _
    (fun i _ => by simpa only [abs_pow] using (pow_le_one₀ (abs_nonneg (z i)) (hz i) : |z i| ^ (e i).val ≤ 1))
    (fun i _ => by simpa only [abs_pow] using (pow_le_one₀ (abs_nonneg (z' i)) (hz' i) : |z' i| ^ (e i).val ≤ 1))).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact (abs_pow_sub_pow_le_unit _ _ (hz i) (hz' i) (e i).val).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt_succ (e i).isLt) (abs_nonneg _))

theorem pointValue_variable_sub_bound (W : Array d V J D) (x : Torus (V × d))
    (z z' : V → ℝ) (hz : ∀ i, |z i| ≤ 1) (hz' : ∀ i, |z' i| ≤ 1) (ζ : J → Bool) :
    |pointValue x z ζ W - pointValue x z' ζ W| ≤ ‖W‖ * ((D : ℝ) * ∑ i, |z i - z' i|) := by
  let C := (D : ℝ) * ∑ i, |z i - z' i|
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hr (r : Row V J D) : |rowWeight r z ζ - rowWeight r z' ζ| ≤ C := by
    simpa only [rowWeight, ← sub_mul, abs_mul, Walsh.abs_character, mul_one] using
      monomial_sub_bound r.1 z z' hz hz'
  calc
    _ = |∑ r, (rowWeight r z ζ - rowWeight r z' ζ) * (toContinuous (W r) x).re| := by
      simp only [pointValue, Finset.sum_sub_distrib, sub_mul]
    _ ≤ ∑ r, |(rowWeight r z ζ - rowWeight r z' ζ) * (toContinuous (W r) x).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, C * ‖W r‖ := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul]
      exact mul_le_mul (hr r) ((Complex.abs_re_le_norm _).trans (evaluate_bound _ _)) (abs_nonneg _) hC
    _ = _ := by rw [← Finset.mul_sum, ← norm_eq_sum]; exact mul_comm _ _

theorem pointValue_variable_sub_bound_centered (W : Array d V J D) (x : Torus (V × d))
    (z z' : V → ℝ) (hz : ∀ i, |z i| ≤ 1) (hz' : ∀ i, |z' i| ≤ 1) (ζ : J → Bool) :
    |pointValue x z ζ W - pointValue x z' ζ W| ≤ ‖W - unit‖ * ((D : ℝ) * ∑ i, |z i - z' i|) := by
  have he := (pointEvaluation x z hz ζ).map_sub W unit
  have he' := (pointEvaluation x z' hz' ζ).map_sub W unit
  simp only [pointEvaluation_apply, pointValue_unit] at he he'
  have hb := pointValue_variable_sub_bound (W - unit) x z z' hz hz' ζ
  rw [he, he'] at hb
  simpa only [sub_sub_sub_cancel_right] using hb

theorem pointValue_sign_sub_bound (S : Finset J) (W : Array d V J D) (x : Torus (V × d))
    (z : V → ℝ) (hz : ∀ i, |z i| ≤ 1) (ζ ζ' : J → Bool)
    (he : ∀ j ∉ S, ζ j = ζ' j) :
    |pointValue x z ζ W - pointValue x z ζ' W| ≤ 2 * ∑ j ∈ S, ‖symbolPart j W‖ := by
  have hr := pointValue_remove_congr S W x z ζ ζ' he
  calc
    _ ≤ |pointValue x z ζ W - pointValue x z ζ (remove S W)| +
        |pointValue x z ζ (remove S W) - pointValue x z ζ' W| := abs_sub_le _ _ _
    _ ≤ (∑ j ∈ S, ‖symbolPart j W‖) + ∑ j ∈ S, ‖symbolPart j W‖ := by
      apply add_le_add (pointValue_remove_error S W x z hz ζ)
      rw [hr, abs_sub_comm]
      exact pointValue_remove_error S W x z hz ζ'
    _ = _ := by ring

theorem pointValue_resample_sub_bound (S : Finset J) (W : Array d V J D) (x : Torus (V × d))
    (z z' : V → ℝ) (hz : ∀ i, |z i| ≤ 1) (hz' : ∀ i, |z' i| ≤ 1)
    (ζ ζ' : J → Bool) (he : ∀ j ∉ S, ζ j = ζ' j) :
    |pointValue x z ζ W - pointValue x z' ζ' W| ≤
      2 * (∑ j ∈ S, ‖symbolPart j W‖) + ‖W - unit‖ * ((D : ℝ) * ∑ i, |z i - z' i|) :=
  (abs_sub_le (pointValue x z ζ W) (pointValue x z ζ' W) (pointValue x z' ζ' W)).trans
    (add_le_add (pointValue_sign_sub_bound S W x z hz ζ ζ' he)
      (pointValue_variable_sub_bound_centered W x z z' hz hz' ζ'))

end CausalLowerbound.PartC.Representative

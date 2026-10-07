import CausalLowerbound.PartC.WalshParity

/-! Finite products in the actual Walsh coefficient space. This explicit
formula needs no ring instance on the retained coefficient arrays. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace CausalLowerbound.PartC.Walsh

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

def scalar (c : ℝ) : Coefficients J := lp.single 1 ∅ c

@[simp] theorem scalar_norm (c : ℝ) : ‖(scalar c : Coefficients J)‖ = |c| := by
  rw [scalar, lp.norm_single (by norm_num), Real.norm_eq_abs]

@[simp] theorem evaluate_scalar (ζ : J → Bool) (c : ℝ) : evaluate ζ (scalar c) = c := by
  simp [scalar]

def finiteProduct (a : ι → Coefficients J) : Coefficients J :=
  ∑ S : ι → Finset J, lp.single 1 (parityUnion S) (∏ i, a i (S i))

theorem finiteProduct_norm (a : ι → Coefficients J) : ‖finiteProduct a‖ ≤ ∏ i, ‖a i‖ := by
  calc
    _ ≤ ∑ S : ι → Finset J, ‖(lp.single 1 (parityUnion S) (∏ i, a i (S i)) : Coefficients J)‖ :=
      norm_sum_le _ _
    _ = ∑ S : ι → Finset J, ∏ i, |a i (S i)| := by
      simp only [lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞)), Real.norm_eq_abs, Finset.abs_prod]
    _ = ∏ i, ∑ S : Finset J, |a i S| :=
      (Fintype.prod_sum (fun (i : ι) (S : Finset J) => |a i S|)).symm
    _ = ∏ i, ‖a i‖ := by
      apply Finset.prod_congr rfl
      intro i _
      exact (norm_eq_sum (a i)).symm

theorem evaluate_finiteProduct (ζ : J → Bool) (a : ι → Coefficients J) :
    evaluate ζ (finiteProduct a) = ∏ i, evaluate ζ (a i) := by
  simp only [finiteProduct, map_sum]
  simp only [evaluate_single, character_parityUnion, ← Finset.prod_mul_distrib]
  simp only [evaluate_apply, tsum_fintype]
  exact (Fintype.prod_sum (fun (i : ι) (S : Finset J) => a i S * character S ζ)).symm

end CausalLowerbound.PartC.Walsh

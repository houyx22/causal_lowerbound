import CausalLowerbound.PartC.WalshFiniteProduct
import CausalLowerbound.PartB.PolarizationAlgebra

/-! Actual Walsh-valued positive-polarization coefficients. They reconstruct
the scalar stencil at every sign vector, and their sum of norms has no
dependence on the number of rough signs. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC.Walsh

open PartB.Polarization

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]

def affineWeight (a : Coefficients J) (θ : ℝ) (b : Bool) : Coefficients J :=
  if b then scalar θ⁻¹ else a - scalar θ⁻¹

theorem evaluate_affineWeight (ζ : J → Bool) (a : Coefficients J) (θ : ℝ) (b : Bool) :
    evaluate ζ (affineWeight a θ b) = affineCoefficient (evaluate ζ a) θ b := by
  cases b <;> simp [affineWeight, affineCoefficient]

theorem affineWeight_norm_sum (a : Coefficients J) (ha : ‖a‖ ≤ 1) (θ : ℝ) :
    (∑ b : Bool, ‖affineWeight a θ b‖) ≤ 1 + 2 * |θ⁻¹| := by
  simp only [Fintype.sum_bool, affineWeight, Bool.true_eq, if_true, Bool.false_eq_true, if_false, scalar_norm]
  have h := norm_sub_le a (scalar θ⁻¹)
  rw [scalar_norm] at h
  linarith

def polarizationWeight (a : ι → Coefficients J) (θ : ℝ) (m : (ι → Bool) × (ι → Bool)) : Coefficients J :=
  positiveWeight m.2 • finiteProduct (fun i => affineWeight (a i) θ (m.1 i))

theorem evaluate_polarizationWeight (ζ : J → Bool) (a : ι → Coefficients J) (θ : ℝ)
    (m : (ι → Bool) × (ι → Bool)) :
    evaluate ζ (polarizationWeight a θ m) = stencilWeight (fun i => evaluate ζ (a i)) θ m := by
  simp only [polarizationWeight, map_smul, smul_eq_mul, evaluate_finiteProduct,
    evaluate_affineWeight, stencilWeight]
  exact mul_comm _ _

theorem polarizationWeight_bound (a : ι → Coefficients J) (ha : ∀ i, ‖a i‖ ≤ 1) (θ : ℝ) :
    (∑ m : (ι → Bool) × (ι → Bool), ‖polarizationWeight a θ m‖) ≤ stencilBound (ι := ι) θ := by
  have hprod : (∑ b : ι → Bool, ∏ i, ‖affineWeight (a i) θ (b i)‖) ≤
      (1 + 2 * |θ⁻¹|) ^ Fintype.card ι := by
    rw [← Fintype.prod_sum (fun (i : ι) (b : Bool) => ‖affineWeight (a i) θ b‖)]
    calc
      _ ≤ ∏ _i : ι, (1 + 2 * |θ⁻¹|) :=
        Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
          (fun i _ => affineWeight_norm_sum (a i) (ha i) θ)
      _ = _ := by simp
  calc
    _ ≤ ∑ m : (ι → Bool) × (ι → Bool), |positiveWeight m.2| *
        ∏ i, ‖affineWeight (a i) θ (m.1 i)‖ := by
      apply Finset.sum_le_sum
      intro m _
      rw [polarizationWeight, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (finiteProduct_norm _) (abs_nonneg _)
    _ = (∑ b : ι → Bool, ∏ i, ‖affineWeight (a i) θ (b i)‖) *
        ∑ p : ι → Bool, |positiveWeight p| := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro p _
      exact mul_comm _ _
    _ ≤ stencilBound (ι := ι) θ := mul_le_mul_of_nonneg_right hprod
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

end CausalLowerbound.PartC.Walsh

import CausalLowerbound.UpperBound.StableInverse
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Matrix estimates in the coefficient sup norm and their continuous
linear-operator interpretation.  No self-adjointness is needed. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

variable {I J : Type*} [Fintype I] [Fintype J]

def matrixOperator (A : Matrix I J ℝ) : (J → ℝ) →L[ℝ] (I → ℝ) :=
  LinearMap.toContinuousLinearMap A.mulVecLin

@[simp] theorem matrixOperator_apply (A : Matrix I J ℝ) (x : J → ℝ) : matrixOperator A x = A *ᵥ x := rfl

theorem matrix_mulVec_norm_le_entries (A : Matrix I J ℝ) {e : ℝ}
    (he : 0 ≤ e) (hA : ∀ i j, |A i j| ≤ e) (x : J → ℝ) :
    ‖A *ᵥ x‖ ≤ Fintype.card J * e * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change |∑ j, A i j * x j| ≤ _
  calc
    _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : J, e * ‖x‖ := Finset.sum_le_sum (fun j _ => by
      rw [abs_mul]
      exact mul_le_mul (hA i j) (norm_le_pi_norm x j) (abs_nonneg _) he)
    _ = _ := by simp [mul_assoc]

theorem matrixOperator_norm_le_entries (A : Matrix I J ℝ) {e : ℝ}
    (he : 0 ≤ e) (hA : ∀ i j, |A i j| ≤ e) :
    ‖matrixOperator A‖ ≤ Fintype.card J * e :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (matrix_mulVec_norm_le_entries A he hA)

def matrixOperatorLinear : Matrix I J ℝ →ₗ[ℝ] ((J → ℝ) →L[ℝ] (I → ℝ)) where
  toFun := matrixOperator
  map_add' := by
    intro A B
    ext x i
    simp only [ContinuousLinearMap.add_apply, matrixOperator_apply, Matrix.add_mulVec, Pi.add_apply]
  map_smul' := by
    intro a A
    ext x i
    simp only [ContinuousLinearMap.smul_apply, matrixOperator_apply, Matrix.smul_mulVec_assoc,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem matrixOperator_continuous : Continuous (matrixOperator (I := I) (J := J)) :=
  matrixOperatorLinear.continuous_of_finiteDimensional

theorem matrixOperator_sub (A B : Matrix I J ℝ) :
    matrixOperator (A - B) = matrixOperator A - matrixOperator B :=
  matrixOperatorLinear.map_sub A B

theorem matrix_quadratic_le (Q : Matrix I I ℝ) (x : I → ℝ) :
    (∑ i, x i * (Q *ᵥ x) i) ≤ Fintype.card I * ‖x‖ * ‖Q *ᵥ x‖ := by
  calc
    _ ≤ ∑ i, |x i * (Q *ᵥ x) i| := Finset.sum_le_sum (fun _ _ => le_abs_self _)
    _ ≤ ∑ _i : I, ‖x‖ * ‖Q *ᵥ x‖ := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm x i) (norm_le_pi_norm (Q *ᵥ x) i)
        (abs_nonneg _) (norm_nonneg _))
    _ = _ := by simp [mul_assoc]

theorem matrix_lower_of_quadratic [Nonempty I] (Q : Matrix I I ℝ) (c : ℝ)
    (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ ∑ i, x i * (Q *ᵥ x) i) (x : I → ℝ) :
    (c / Fintype.card I) * ‖x‖ ≤ ‖Q *ᵥ x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hK : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hb := (hQ x).trans (matrix_quadratic_le Q x)
  have hc : c * ‖x‖ ≤ Fintype.card I * ‖Q *ᵥ x‖ := by
    apply (mul_le_mul_right hn).mp
    nlinarith [hb]
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  simpa only [mul_comm] using hc

theorem matrix_lower_of_entry_perturbation (G Q : Matrix I I ℝ) (c : ℝ) {e : ℝ}
    (he : 0 ≤ e) (hG : ∀ x, c * ‖x‖ ≤ ‖G *ᵥ x‖)
    (hE : ∀ i j, |Q i j - G i j| ≤ e) (x : I → ℝ) :
    (c - Fintype.card I * e) * ‖x‖ ≤ ‖Q *ᵥ x‖ := by
  have hp := matrix_mulVec_norm_le_entries (Q - G) he hE x
  rw [Matrix.sub_mulVec] at hp
  have ht : ‖G *ᵥ x‖ ≤ ‖Q *ᵥ x‖ + ‖Q *ᵥ x - G *ᵥ x‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le (Q *ᵥ x) (Q *ᵥ x - G *ᵥ x)
  nlinarith [hG x]

end CausalLowerbound.UpperBound

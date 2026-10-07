import CausalLowerbound.PartC.WalshParity

/-! The isometric Walsh coefficient reflection implements simultaneous
sign flip and will supply the reflected half of each paired carrier label. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC.Walsh

variable {J : Type*} [Fintype J] [DecidableEq J]

def reflection : Coefficients J →L[ℝ] Coefficients J :=
  multiplier (fun S => (-1 : ℝ) ^ S.card) (fun S => by simp)

@[simp] theorem reflection_apply (a : Coefficients J) (S : Finset J) :
    reflection a S = a S * (-1 : ℝ) ^ S.card := multiplier_apply _ _ a S

@[simp] theorem reflection_involution (a : Coefficients J) : reflection (reflection a) = a := by
  apply lp.ext
  funext S
  simp only [reflection_apply, mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

@[simp] theorem reflection_norm (a : Coefficients J) : ‖reflection a‖ = ‖a‖ := by
  simp only [norm_eq_sum, reflection_apply, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]

theorem evaluate_reflection (ζ : J → Bool) (a : Coefficients J) :
    evaluate ζ (reflection a) = evaluate (flip ζ) a := by
  simp only [evaluate_apply, tsum_fintype, reflection_apply, character_flip, mul_assoc]

variable {I : Type*} [Fintype I]

def vectorReflection : (I → Coefficients J) →L[ℝ] (I → Coefficients J) :=
  ContinuousLinearMap.pi (fun i => reflection.comp (ContinuousLinearMap.proj i))

@[simp] theorem vectorReflection_apply (a : I → Coefficients J) (i : I) :
    vectorReflection a i = reflection (a i) := rfl

@[simp] theorem vectorReflection_involution (a : I → Coefficients J) :
    vectorReflection (vectorReflection a) = a := by
  funext i
  exact reflection_involution (a i)

@[simp] theorem vectorReflection_norm (a : I → Coefficients J) : ‖vectorReflection a‖ = ‖a‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr (fun i => by
      simpa only [vectorReflection_apply, reflection_norm] using norm_le_pi_norm a i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (vectorReflection a))).mpr
    intro i
    simpa only [vectorReflection_apply, reflection_norm] using norm_le_pi_norm (vectorReflection a) i

end CausalLowerbound.PartC.Walsh

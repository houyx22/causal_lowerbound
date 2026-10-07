import CausalLowerbound.PartC.RepresentativeEvaluation
import CausalLowerbound.PartC.WalshParity

/-! The coefficient involution realizes simultaneous reflection of the rough
variables and the signs. Symmetrization retains both the norm and symbol bounds. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC.Representative

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

theorem monomial_neg (e : Degree ι D) (z : ι → ℝ) :
    monomial e (fun i => -z i) = (-1) ^ degreeSize e * monomial e z := by
  change (∏ i, (-z i) ^ (e i).val) = _
  calc
    _ = ∏ i, ((-1 : ℝ) ^ (e i).val * z i ^ (e i).val) :=
      Finset.prod_congr rfl (fun i _ => neg_pow (z i) (e i).val)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rfl

theorem rowWeight_neg_flip (r : Row ι J D) (z : ι → ℝ) (ζ : J → Bool) :
    rowWeight r (fun i => -z i) (Walsh.flip ζ) = rowSign r * rowWeight r z ζ := by
  simp only [rowWeight, monomial_neg, Walsh.character_flip, rowSign, pow_add]
  ring

theorem pointValue_reflection (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool)
    (a : Array d ι J D) : pointValue x z ζ (reflection a) =
      pointValue x (fun i => -z i) (Walsh.flip ζ) a := by
  simp only [pointValue, reflection_apply, Wiener.toContinuous_real_smul,
    ContinuousMap.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, rowWeight_neg_flip]
  apply Finset.sum_congr rfl
  intro r _
  ring

def evenPart : Array d ι J D →L[ℝ] Array d ι J D :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ (Array d ι J D) +
    (reflection : Array d ι J D →L[ℝ] Array d ι J D))

@[simp] theorem evenPart_apply (a : Array d ι J D) :
    evenPart a = (1 / 2 : ℝ) • (a + reflection a) := rfl

@[simp] theorem reflection_evenPart (a : Array d ι J D) : reflection (evenPart a) = evenPart a := by
  simp only [evenPart_apply, map_smul, map_add, reflection_involution]
  rw [add_comm]

theorem evenPart_bound (a : Array d ι J D) : ‖evenPart a‖ ≤ ‖a‖ := by
  rw [evenPart_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2)]
  have h := norm_add_le a (reflection a)
  rw [reflection_norm] at h
  linarith

@[simp] theorem evenPart_unit : evenPart (unit : Array d ι J D) = unit := by
  rw [evenPart_apply, reflection_unit, ← two_smul ℝ unit, smul_smul]
  norm_num

theorem symbolPart_evenPart (j : J) (a : Array d ι J D) :
    symbolPart j (evenPart a) = evenPart (symbolPart j a) := by
  simp only [evenPart_apply, map_smul, map_add, symbolPart_reflection]

theorem symbolPart_evenPart_bound (j : J) (a : Array d ι J D) :
    ‖symbolPart j (evenPart a)‖ ≤ ‖symbolPart j a‖ := by
  rw [symbolPart_evenPart]
  exact evenPart_bound _

end CausalLowerbound.PartC.Representative

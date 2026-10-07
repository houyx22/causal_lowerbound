import CausalLowerbound.PartC.CubicSitePolynomial
import CausalLowerbound.PartC.OutcomeLikelihoodPolynomials
import CausalLowerbound.PartC.AssignedOutcomeBridge

/-! Evaluating the actual cubic Taylor factors through the cubic target
gives exactly the normalized single-site design bridge in every row. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative RoughOutcome
variable {V d J : Type*} [Fintype V] [DecidableEq V]
  [Fintype d] [Fintype J] [DecidableEq J]

def outcomeTaylorCoefficient (R T shift jb η smooth rough : ℝ) (f : Fin 4) : ℝ :=
  if f = 0 then likelihood R T jb η smooth rough
  else if f = 1 then incrementOne R T shift jb η smooth rough
  else if f = 2 then incrementTwo R T shift jb smooth rough
  else incrementThree R T shift jb rough

theorem outcomeTaylorPolynomial_eq_sum (R T shift jb η smooth rough : ℝ) (p : MvPolynomial V ℝ) :
    outcomeTaylorPolynomial R T shift jb η smooth rough p =
      ∑ f : Fin 4, C (outcomeTaylorCoefficient R T shift jb η smooth rough f) * p ^ f.val := by
  simp [Fin.sum_univ_succ, outcomeTaylorCoefficient, outcomeTaylorPolynomial]
  <;> ring

theorem outcomeTaylorCoefficient_slot_sum (R T shift jb η smooth rough scale v : ℝ) (f : Fin 4) :
    (∑ e : Fin 4, outcomeTaylorCoefficient R T shift jb η smooth rough e *
      (if e = 0 then (scale * rough) ^ f.val else
        Representative.outcomeMoment (scale ^ 2 * v) f * (scale * rough) ^ e.val)) =
      (scale * rough) ^ f.val * likelihood R T jb η smooth rough +
        normalizedIncrement f scale v R T shift jb η smooth rough := by
  simp [Fin.sum_univ_succ, outcomeTaylorCoefficient, normalizedIncrement, normalizedSubstitution]
  <;> ring

theorem outcomePolynomialFunctional_taylor (v scale R T shift jb η smooth rough : V → ℝ)
    (W : Representative.Array d V J 3) (u : V × d → ℝ) (ζ : J → Bool) :
    outcomePolynomialFunctional (fun i => scale i ^ 2 * v i) W u (fun i => scale i * rough i) ζ
      (∏ i, outcomeTaylorPolynomial (R i) (T i) (shift i) (jb i) (η i) (smooth i) (rough i) (X i)) =
      ∑ r : Row V J 3, Walsh.character r.2 ζ * (Wiener.toContinuous (W r) (Wiener.torusProjection u)).re *
        ∏ i, ((scale i * rough i) ^ (r.1 i).val * likelihood (R i) (T i) (jb i) (η i) (smooth i) (rough i) +
          normalizedIncrement (r.1 i) (scale i) (v i) (R i) (T i) (shift i) (jb i) (η i) (smooth i) (rough i)) := by
  simp_rw [outcomeTaylorPolynomial_eq_sum, outcomePolynomialFunctional_cubic, outcomeTaylorCoefficient_slot_sum]

end CausalLowerbound.PartC

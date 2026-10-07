import CausalLowerbound.PartC.WalshCoefficients
import CausalLowerbound.PartB.SignMonomials

/-! Removing local signs is a coefficient projection and is exactly averaging
over fresh independent signs. Its error is controlled by the sum of the symbol
seminorms, with no dependence on the size of the sign sample space. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC.Walsh

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem norm_eq_sum (a : Coefficients J) : ‖a‖ = ∑ S, |a S| := by
  rw [Wiener.norm_eq_tsum, tsum_fintype]
  simp only [Real.norm_eq_abs]

def remove (T : Finset J) : Coefficients J →L[ℝ] Coefficients J :=
  project (fun S => Disjoint S T)

def symbolPart (j : J) : Coefficients J →L[ℝ] Coefficients J :=
  project (fun S => j ∈ S)

@[simp] theorem remove_apply (T : Finset J) (a : Coefficients J) (S : Finset J) :
    remove T a S = if Disjoint S T then a S else 0 := project_apply _ _ _

@[simp] theorem symbolPart_apply (j : J) (a : Coefficients J) (S : Finset J) :
    symbolPart j a S = if j ∈ S then a S else 0 := project_apply _ _ _

theorem remove_bound (T : Finset J) (a : Coefficients J) : ‖remove T a‖ ≤ ‖a‖ :=
  project_bound _ _

theorem symbolPart_bound (j : J) (a : Coefficients J) : ‖symbolPart j a‖ ≤ ‖a‖ :=
  project_bound _ _

theorem removal_error (T : Finset J) (a : Coefficients J) :
    ‖a - remove T a‖ ≤ ∑ j ∈ T, ‖symbolPart j a‖ := by
  have hterm (S : Finset J) : |a S - remove T a S| ≤ ∑ j ∈ T, |symbolPart j a S| := by
    rw [remove_apply]
    by_cases h : Disjoint S T
    · rw [if_pos h, sub_self, abs_zero]
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    · obtain ⟨j, hjS, hjT⟩ := Finset.not_disjoint_iff.mp h
      rw [if_neg h, sub_zero]
      calc
        _ = |symbolPart j a S| := by rw [symbolPart_apply, if_pos hjS]
        _ ≤ _ := Finset.single_le_sum (f := fun j => |symbolPart j a S|)
          (fun _ _ => abs_nonneg _) hjT
  calc
    _ = ∑ S, |a S - remove T a S| := by rw [norm_eq_sum]; rfl
    _ ≤ ∑ S : Finset J, ∑ j ∈ T, |symbolPart j a S| :=
      Finset.sum_le_sum (fun S _ => hterm S)
    _ = ∑ j ∈ T, ‖symbolPart j a‖ := by
      rw [Finset.sum_comm]
      simp only [norm_eq_sum]

theorem evaluate_remove_congr (T : Finset J) (a : Coefficients J) (ζ ζ' : J → Bool)
    (h : ∀ j ∉ T, ζ j = ζ' j) : evaluate ζ (remove T a) = evaluate ζ' (remove T a) := by
  simp only [evaluate_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro S _
  rw [remove_apply]
  by_cases hST : Disjoint S T
  · rw [if_pos hST, character_congr S ζ ζ' (fun j hj =>
      h j (Finset.disjoint_left.mp hST hj))]
  · simp [hST]

theorem evaluate_removal_error (T : Finset J) (a : Coefficients J) (ζ : J → Bool) :
    |evaluate ζ a - evaluate ζ (remove T a)| ≤ ∑ j ∈ T, ‖symbolPart j a‖ := by
  rw [← map_sub]
  exact (evaluate_bound ζ _).trans (removal_error T a)

def resample (T : Finset J) (ζ fresh : J → Bool) (j : J) : Bool :=
  if j ∈ T then fresh j else ζ j

theorem character_eq_prod (S : Finset J) (ζ : J → Bool) :
    character S ζ = ∏ j, if j ∈ S then PartB.sign (ζ j) else 1 := by
  rw [← Finset.prod_filter]
  simp [character]

theorem character_resample_expect (S T : Finset J) (ζ : J → Bool) :
    PartB.independentSigns.expect (fun fresh => character S (resample T ζ fresh)) =
      if Disjoint S T then character S ζ else 0 := by
  have hprod : PartB.independentSigns.expect (fun fresh =>
      character S (resample T ζ fresh)) =
      (FiniteLaw.independent (fun _ : J => PartB.rademacher)).expect
        (fun fresh => ∏ j, if j ∈ S then
          PartB.sign (if j ∈ T then fresh j else ζ j) else 1) := by
    apply FiniteLaw.expect_congr
    intro fresh
    exact character_eq_prod S _
  rw [hprod, FiniteLaw.expect_independent_prod (fun _ : J => PartB.rademacher)
    (fun j b => if j ∈ S then PartB.sign (if j ∈ T then b else ζ j) else 1)]
  have hfactor (j : J) : PartB.rademacher.expect
      (fun b => if j ∈ S then PartB.sign (if j ∈ T then b else ζ j) else 1) =
      if j ∈ S then if j ∈ T then 0 else PartB.sign (ζ j) else 1 := by
    by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;>
      simp [hS, hT, PartB.rademacher_expect, PartB.sign]
  simp_rw [hfactor]
  by_cases hST : Disjoint S T
  · rw [if_pos hST, character_eq_prod]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hS : j ∈ S
    · simp [hS, Finset.disjoint_left.mp hST hS]
    · simp [hS]
  · rw [if_neg hST]
    obtain ⟨j, hjS, hjT⟩ := Finset.not_disjoint_iff.mp hST
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hjS, hjT])

/-- The projection is the actual conditional expectation under the finite
independent Rademacher law, retaining the signs outside T. -/
theorem evaluate_remove_eq_expect (T : Finset J) (a : Coefficients J) (ζ : J → Bool) :
    evaluate ζ (remove T a) =
      PartB.independentSigns.expect (fun fresh => evaluate (resample T ζ fresh) a) := by
  have hsum : PartB.independentSigns.expect (fun fresh =>
      ∑ S, a S * character S (resample T ζ fresh)) =
      ∑ S, a S * PartB.independentSigns.expect
        (fun fresh => character S (resample T ζ fresh)) := by
    simp only [FiniteLaw.expect, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S _
    apply Finset.sum_congr rfl
    intro fresh _
    ring
  simp only [evaluate_apply, tsum_fintype]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro S _
  rw [character_resample_expect, remove_apply]
  split_ifs <;> simp

end CausalLowerbound.PartC.Walsh

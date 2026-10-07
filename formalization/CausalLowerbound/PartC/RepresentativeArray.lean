import CausalLowerbound.PartC.FiniteL1Array
import CausalLowerbound.PartC.WalshCoefficients
import CausalLowerbound.WienerAlgebra

/-! Normalized polynomial--Walsh representatives. A row stores the Fourier
coefficient multiplied by the degree weight. Equality is equality of these
arrays, and does not identify representatives having the same evaluation. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace CausalLowerbound.PartC.Representative

abbrev Degree (ι : Type*) (D : ℕ) := ι → Fin (D + 1)
abbrev Row (ι J : Type*) (D : ℕ) := Degree ι D × Finset J
abbrev Array (d ι J : Type*) (D : ℕ) := FiniteL1.Family (Row ι J D) (Wiener.Fourier (ι × d))

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

def zeroRow : Row ι J D := (0, ∅)

def degreeSize (e : Degree ι D) : ℕ := ∑ i, (e i).val

def rowSign (r : Row ι J D) : ℝ := (-1) ^ (degreeSize r.1 + r.2.card)

@[simp] theorem rowSign_abs (r : Row ι J D) : |rowSign r| = 1 := by
  simp [rowSign]

@[simp] theorem rowSign_square (r : Row ι J D) : rowSign r * rowSign r = 1 := by
  rw [rowSign, ← pow_two, ← pow_mul, Nat.mul_comm _ 2, pow_mul]
  norm_num

@[simp] theorem rowSign_zero : rowSign (zeroRow : Row ι J D) = 1 := by
  simp [rowSign, zeroRow, degreeSize]

def unit : Array d ι J D := lp.single 1 zeroRow 1

@[simp] theorem unit_norm : ‖(unit : Array d ι J D)‖ = 1 := by
  rw [unit, lp.norm_single (by norm_num), norm_one]

theorem norm_eq_sum (a : Array d ι J D) : ‖a‖ = ∑ r, ‖a r‖ := FiniteL1.norm_eq_sum a

def reflection : Array d ι J D →L[ℝ] Array d ι J D :=
  FiniteL1.diagonal (fun r => rowSign r • ContinuousLinearMap.id ℝ (Wiener.Fourier (ι × d)))
    1 (fun r a => by simp [norm_smul, Real.norm_eq_abs])

@[simp] theorem reflection_apply (a : Array d ι J D) (r : Row ι J D) :
    reflection a r = rowSign r • a r := by
  simp [reflection]

@[simp] theorem reflection_involution (a : Array d ι J D) : reflection (reflection a) = a := by
  apply lp.ext
  funext r
  simp [smul_smul]

@[simp] theorem reflection_norm (a : Array d ι J D) : ‖reflection a‖ = ‖a‖ := by
  rw [norm_eq_sum, norm_eq_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp [norm_smul, Real.norm_eq_abs]

@[simp] theorem reflection_unit : reflection (unit : Array d ι J D) = unit := by
  apply lp.ext
  funext r
  rw [reflection_apply]
  by_cases h : r = zeroRow
  · subst r
    simp
  · simp [unit, Pi.single_apply, h]

def symbolPart (j : J) : Array d ι J D →L[ℝ] Array d ι J D :=
  FiniteL1.project (fun r => j ∈ r.2)

def remove (T : Finset J) : Array d ι J D →L[ℝ] Array d ι J D :=
  FiniteL1.project (fun r => Disjoint r.2 T)

@[simp] theorem symbolPart_apply (j : J) (a : Array d ι J D) (r : Row ι J D) :
    symbolPart j a r = if j ∈ r.2 then a r else 0 := FiniteL1.project_apply _ _ _

@[simp] theorem remove_apply (T : Finset J) (a : Array d ι J D) (r : Row ι J D) :
    remove T a r = if Disjoint r.2 T then a r else 0 := FiniteL1.project_apply _ _ _

theorem symbolPart_bound (j : J) (a : Array d ι J D) : ‖symbolPart j a‖ ≤ ‖a‖ :=
  FiniteL1.project_bound _ _

theorem remove_bound (T : Finset J) (a : Array d ι J D) : ‖remove T a‖ ≤ ‖a‖ :=
  FiniteL1.project_bound _ _

theorem symbolPart_norm (j : J) (a : Array d ι J D) :
    ‖symbolPart j a‖ = ∑ r, if j ∈ r.2 then ‖a r‖ else 0 := FiniteL1.project_norm _ _

@[simp] theorem symbolPart_unit (j : J) : symbolPart j (unit : Array d ι J D) = 0 := by
  apply lp.ext
  funext r
  rw [symbolPart_apply]
  by_cases h : r = zeroRow
  · subst r
    simp [zeroRow]
  · simp [unit, Pi.single_apply, h]

theorem symbolPart_reflection (j : J) (a : Array d ι J D) :
    symbolPart j (reflection a) = reflection (symbolPart j a) := by
  apply lp.ext
  funext r
  simp only [symbolPart_apply, reflection_apply]
  split_ifs <;> simp

theorem removal_error (T : Finset J) (a : Array d ι J D) :
    ‖a - remove T a‖ ≤ ∑ j ∈ T, ‖symbolPart j a‖ := by
  have hterm (r : Row ι J D) : ‖a r - remove T a r‖ ≤ ∑ j ∈ T, ‖symbolPart j a r‖ := by
    rw [remove_apply]
    by_cases h : Disjoint r.2 T
    · rw [if_pos h, sub_self, norm_zero]
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    · obtain ⟨j, hjS, hjT⟩ := Finset.not_disjoint_iff.mp h
      rw [if_neg h, sub_zero]
      calc
        _ = ‖symbolPart j a r‖ := by rw [symbolPart_apply, if_pos hjS]
        _ ≤ _ := Finset.single_le_sum (f := fun j => ‖symbolPart j a r‖)
          (fun _ _ => norm_nonneg _) hjT
  calc
    _ = ∑ r, ‖a r - remove T a r‖ := by rw [norm_eq_sum]; rfl
    _ ≤ ∑ r : Row ι J D, ∑ j ∈ T, ‖symbolPart j a r‖ :=
      Finset.sum_le_sum (fun r _ => hterm r)
    _ = ∑ j ∈ T, ‖symbolPart j a‖ := by
      rw [Finset.sum_comm]
      simp only [norm_eq_sum]

end CausalLowerbound.PartC.Representative

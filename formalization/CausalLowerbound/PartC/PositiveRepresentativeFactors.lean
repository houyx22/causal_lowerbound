import CausalLowerbound.PartC.RepresentativeFactors

/-! Positive affine atoms in the actual one-slot representative space. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace CausalLowerbound.PartC.Representative

variable {d J : Type*} [Fintype d] [Fintype J] [DecidableEq J] {D : ℕ}

def factorUnit : Factor d J D := lp.single 1 (0, ∅) 1

@[simp] theorem factorUnit_norm : ‖(factorUnit : Factor d J D)‖ = 1 := by
  rw [factorUnit, lp.norm_single (by norm_num), norm_one]

@[simp] theorem factorUnit_value (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool) :
    factorValue x z ζ (factorUnit : Factor d J D) = 1 := by
  rw [factorUnit, factorValue_single]
  simp [Wiener.toContinuous_one]

@[simp] theorem factorSymbol_factorUnit (j : J) : factorSymbol j (factorUnit : Factor d J D) = 0 := by
  apply lp.ext
  funext r
  rw [factorSymbol_apply]
  by_cases hr : r = (0, ∅)
  · subst r
    simp
  · simp [factorUnit, Pi.single_apply, hr]

def positiveFactor (θ : ℝ) (a : Factor d J D) : Factor d J D := factorUnit + θ • a

theorem positiveFactor_norm (θ : ℝ) (a : Factor d J D) (ha : ‖a‖ ≤ 1) :
    ‖positiveFactor θ a‖ ≤ 1 + |θ| := by
  calc
    _ ≤ ‖(factorUnit : Factor d J D)‖ + ‖θ • a‖ := norm_add_le _ _
    _ ≤ 1 + |θ| := by
      rw [factorUnit_norm, norm_smul, Real.norm_eq_abs]
      exact add_le_add_left (mul_le_of_le_one_right (abs_nonneg _) ha) _

theorem positiveFactor_value (θ : ℝ) (a : Factor d J D) (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool) :
    factorValue x z ζ (positiveFactor θ a) = 1 + θ • factorValue x z ζ a := by
  rw [← factorEvaluation_apply]
  rw [positiveFactor, map_add, map_smul, factorEvaluation_apply, factorEvaluation_apply, factorUnit_value]

theorem positiveFactor_range (θ : ℝ) (a : Factor d J D) (ha : ‖a‖ ≤ 1)
    (x : Wiener.Torus d) (z : ℝ) (hz : |z| ≤ 1) (ζ : J → Bool) :
    1 - |θ| ≤ (factorValue x z ζ (positiveFactor θ a)).re ∧
      (factorValue x z ζ (positiveFactor θ a)).re ≤ 1 + |θ| := by
  have h : |(factorValue x z ζ a).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans ((factorValue_bound x z hz ζ a).trans ha)
  have hmul : |θ * (factorValue x z ζ a).re| ≤ |θ| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) h
  rw [positiveFactor_value]
  simp only [Complex.add_re, Complex.one_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rcases abs_le.mp hmul with ⟨hl, hu⟩
  constructor <;> linarith

theorem positiveFactor_real (θ : ℝ) (a : Factor d J D) (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool)
    (ha : (factorValue x z ζ a).im = 0) : (factorValue x z ζ (positiveFactor θ a)).im = 0 := by
  rw [positiveFactor_value]
  simp [Complex.real_smul, Complex.mul_im, ha]

theorem positiveFactor_symbol (j : J) (θ : ℝ) (a : Factor d J D) :
    ‖factorSymbol j (positiveFactor θ a)‖ = |θ| * ‖factorSymbol j a‖ := by
  rw [positiveFactor, map_add, factorSymbol_factorUnit, zero_add, map_smul, norm_smul, Real.norm_eq_abs]

end CausalLowerbound.PartC.Representative

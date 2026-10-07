import CausalLowerbound.PartC.BlockCoefficientShift

/-! A taper multiplies exactly the nonempty site patterns. Keeping the
empty weight unchanged reproduces the carrier's baseline moment plus
its tapered polynomial increment. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial
variable {A V Ω : Type*} [Fintype A] [DecidableEq A]
  [Fintype V] [DecidableEq V] [Fintype Ω]

def taperedPatternWeight (χ : ℝ) (w : Finset V → ℝ) (S : Finset V) : ℝ :=
  if S = ∅ then w ∅ else χ * w S

@[simp] theorem taperedPatternWeight_empty (χ : ℝ) (w : Finset V → ℝ) :
    taperedPatternWeight χ w ∅ = w ∅ := by simp [taperedPatternWeight]

theorem sitePatternFunctional_replace_empty (a χ : ℝ) (w : Finset V → ℝ)
    (p : MvPolynomial V ℝ) :
    sitePatternFunctional (fun S => if S = ∅ then a else χ * w S) p =
      χ * sitePatternFunctional w p + (a - χ * w ∅) * constantCoeff p := by
  let L := sitePatternFunctional (fun S => if S = ∅ then a else χ * w S)
  let R : MvPolynomial V ℝ →ₗ[ℝ] ℝ :=
    χ • sitePatternFunctional w + (a - χ * w ∅) • (aeval (fun _ : V => (0 : ℝ))).toLinearMap
  have hR (q : MvPolynomial V ℝ) :
      R q = χ * sitePatternFunctional w q + (a - χ * w ∅) * constantCoeff q := by
    change χ * sitePatternFunctional w q + (a - χ * w ∅) * eval (fun _ => 0) q = _
    rw [eval_zero']
  change L p = _
  rw [← hR p, polynomial_linear_expansion L p, polynomial_linear_expansion R p]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  rw [hR]
  simp only [L, sitePatternFunctional_monomial, one_mul, constantCoeff_monomial]
  by_cases hm : m = 0
  · subst m
    simp only [Finsupp.zero_apply, zero_le_one, implies_true, if_true, Finsupp.support_zero,
      mul_one]
    ring
  · have hs : m.support ≠ ∅ := fun h => hm (Finsupp.support_eq_empty.mp h)
    rw [if_neg hm, if_neg hs, mul_zero, add_zero]
    split_ifs <;> simp

theorem taperedSiteFunctional_shift_average (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (c : A → V → ℝ) (amp χ : ℝ) (w : Finset V → ℝ) (p : MvPolynomial A ℝ) :
    sitePatternFunctional (taperedPatternWeight χ w) (coefficientShiftAverage μ U c amp p) =
      w ∅ * μ.expect (fun ω => eval (U ω) p) +
        χ * sitePatternFunctional w (coefficientShiftPolynomial μ U c amp p) := by
  change sitePatternFunctional (fun S => if S = ∅ then w ∅ else χ * w S)
    (coefficientShiftAverage μ U c amp p) = _
  rw [sitePatternFunctional_replace_empty, coefficientShiftAverage_constantCoeff,
    coefficientShiftPolynomial_eq_average_sub, map_sub, sitePatternFunctional_C]
  ring

theorem taperedSiteFunctional_mask_amplitude (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (c : A → V → ℝ) (amp χ : ℝ) (w : Finset V → ℝ) (p : MvPolynomial A ℝ) :
    sitePatternFunctional (taperedPatternWeight χ w) (coefficientShiftAverage μ U c amp p) =
      sitePatternFunctional (taperedPatternWeight χ w)
        (coefficientShiftAverage μ U c (if χ = 0 then 0 else amp) p) := by
  by_cases hχ : χ = 0
  · rw [if_pos hχ, taperedSiteFunctional_shift_average, taperedSiteFunctional_shift_average]
    simp only [hχ, zero_mul, add_zero]
  · rw [if_neg hχ]

end CausalLowerbound.PartC

import CausalLowerbound.PartC.OutcomePolynomialTarget
import CausalLowerbound.PartC.BlockCoefficientShift

/-! A cubic taper preserves the zero-degree pattern and multiplies
every nonzero pattern. Thus the full coefficient moment includes the
baseline with weight one, even where the taper vanishes. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative
variable {A V Ω : Type*} [Fintype A] [DecidableEq A]
  [Fintype V] [DecidableEq V] [Fintype Ω]

def taperedCubicWeight (χ : ℝ) (w : Degree V 3 → ℝ) (e : Degree V 3) : ℝ :=
  if e = 0 then w 0 else χ * w e

@[simp] theorem taperedCubicWeight_zero (χ : ℝ) (w : Degree V 3 → ℝ) :
    taperedCubicWeight χ w 0 = w 0 := by simp [taperedCubicWeight]

theorem cubicSiteDegree_eq_zero_iff (m : V →₀ ℕ) (hm : ∀ v, m v ≤ 3) :
    cubicSiteDegree m hm = 0 ↔ m = 0 := by
  constructor
  · intro he
    ext v
    exact congrArg Fin.val (congrFun he v)
  · intro he
    subst m
    rfl

theorem cubicSiteFunctional_replace_zero (a χ : ℝ) (w : Degree V 3 → ℝ)
    (p : MvPolynomial V ℝ) :
    cubicSiteFunctional (fun e => if e = 0 then a else χ * w e) p =
      χ * cubicSiteFunctional w p + (a - χ * w 0) * constantCoeff p := by
  let L := cubicSiteFunctional (fun e => if e = 0 then a else χ * w e)
  let R : MvPolynomial V ℝ →ₗ[ℝ] ℝ :=
    χ • cubicSiteFunctional w + (a - χ * w 0) • (aeval (fun _ : V => (0 : ℝ))).toLinearMap
  have hR (q : MvPolynomial V ℝ) :
      R q = χ * cubicSiteFunctional w q + (a - χ * w 0) * constantCoeff q := by
    change χ * cubicSiteFunctional w q + (a - χ * w 0) * eval (fun _ => 0) q = _
    rw [eval_zero']
  change L p = _
  rw [← hR p, polynomial_linear_expansion L p, polynomial_linear_expansion R p]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  rw [hR]
  simp only [L, cubicSiteFunctional_monomial, one_mul, constantCoeff_monomial]
  by_cases hm : m = 0
  · subst m
    simp only [Finsupp.zero_apply, Nat.zero_le, implies_true, dite_true, if_true, mul_one]
    change (if (0 : Degree V 3) = 0 then a else χ * w 0) = χ * w 0 + (a - χ * w 0)
    rw [if_pos rfl]
    ring
  · rw [if_neg hm, mul_zero, add_zero]
    by_cases hd : ∀ v, m v ≤ 3
    · rw [dif_pos hd, dif_pos hd, if_neg (fun he => hm ((cubicSiteDegree_eq_zero_iff m hd).mp he))]
    · rw [dif_neg hd, dif_neg hd, mul_zero]

theorem taperedCubicFunctional_shift_average (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (c : A → V → ℝ) (amp χ : ℝ) (w : Degree V 3 → ℝ) (p : MvPolynomial A ℝ) :
    cubicSiteFunctional (taperedCubicWeight χ w) (coefficientShiftAverage μ U c amp p) =
      w 0 * μ.expect (fun ω => eval (U ω) p) +
        χ * cubicSiteFunctional w (coefficientShiftPolynomial μ U c amp p) := by
  change cubicSiteFunctional (fun e => if e = 0 then w 0 else χ * w e)
    (coefficientShiftAverage μ U c amp p) = _
  rw [cubicSiteFunctional_replace_zero, coefficientShiftAverage_constantCoeff,
    coefficientShiftPolynomial_eq_average_sub, map_sub, cubicSiteFunctional_C]
  change _ = w 0 * _ + χ * (_ - _ * w 0)
  ring

theorem taperedCubicFunctional_mask_amplitude (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (c : A → V → ℝ) (amp χ : ℝ) (w : Degree V 3 → ℝ) (p : MvPolynomial A ℝ) :
    cubicSiteFunctional (taperedCubicWeight χ w) (coefficientShiftAverage μ U c amp p) =
      cubicSiteFunctional (taperedCubicWeight χ w)
        (coefficientShiftAverage μ U c (if χ = 0 then 0 else amp) p) := by
  by_cases hχ : χ = 0
  · rw [if_pos hχ, taperedCubicFunctional_shift_average, taperedCubicFunctional_shift_average]
    simp only [hχ, zero_mul, add_zero]
  · rw [if_neg hχ]

end CausalLowerbound.PartC

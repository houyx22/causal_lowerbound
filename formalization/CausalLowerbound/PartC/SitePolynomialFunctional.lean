import CausalLowerbound.PartC.PolynomialShiftExpansion
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! A linear functional on actual site polynomials. It retains precisely
the square-free monomials and assigns each retained site set its prescribed
design-weighted value. Repeated uses of a site are removed algebraically. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB MvPolynomial
variable {K V Ω : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V] [Fintype Ω]

def siteOccurrenceExponent (sites : K → V) : V →₀ ℕ :=
  ∑ k, Finsupp.single (sites k) 1

theorem siteOccurrenceExponent_apply (sites : K → V) (i : V) :
    siteOccurrenceExponent sites i = (Finset.univ.filter (fun k => sites k = i)).card := by
  simp [siteOccurrenceExponent, Finsupp.single_apply, Finset.sum_boole]

theorem siteOccurrenceExponent_support (sites : K → V) :
    (siteOccurrenceExponent sites).support = Finset.univ.image sites := by
  ext i
  rw [Finsupp.mem_support_iff, siteOccurrenceExponent_apply, Nat.ne_zero_iff_zero_lt, Finset.card_pos]
  simp [Finset.Nonempty]

theorem siteOccurrenceExponent_le_one_iff (sites : K → V) :
    (∀ i, siteOccurrenceExponent sites i ≤ 1) ↔ Function.Injective sites := by
  simp only [siteOccurrenceExponent_apply, Finset.card_le_one, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · intro h a b hab
    exact h (sites a) a rfl b hab.symm
  · intro h i a ha b hb
    exact h (ha.trans hb.symm)

def sitePatternFunctional (w : Finset V → ℝ) : MvPolynomial V ℝ →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun e : V →₀ ℕ => if ∀ i, e i ≤ 1 then w e.support else 0)

theorem sitePatternFunctional_monomial (w : Finset V → ℝ) (e : V →₀ ℕ) (c : ℝ) :
    sitePatternFunctional w (MvPolynomial.monomial e c) =
      c * (if ∀ i, e i ≤ 1 then w e.support else 0) := by
  exact Finsupp.linearCombination_single ℝ c e

theorem sitePatternFunctional_prod_X (w : Finset V → ℝ) (sites : K → V) :
    sitePatternFunctional w (∏ k, X (sites k)) =
      if Function.Injective sites then w (Finset.univ.image sites) else 0 := by
  have he : (∏ k, X (sites k) : MvPolynomial V ℝ) =
      MvPolynomial.monomial (siteOccurrenceExponent sites) 1 := by
    exact (MvPolynomial.monomial_sum_one Finset.univ (fun k => Finsupp.single (sites k) 1)).symm
  simp only [he, sitePatternFunctional_monomial, one_mul, siteOccurrenceExponent_le_one_iff,
    siteOccurrenceExponent_support]

theorem sitePatternFunctional_C (w : Finset V → ℝ) (c : ℝ) :
    sitePatternFunctional w (C c) = c * w ∅ := by
  simpa only [Finsupp.zero_apply, zero_le_one, implies_true, if_true, Finsupp.support_zero] using
    sitePatternFunctional_monomial w 0 c

def wordShiftPolynomial (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (c : K → V → ℝ) (amp : ℝ) :
    MvPolynomial V ℝ :=
  (∑ ω, C (μ.weight ω) * ∏ k, (C (U ω k) + ∑ i, C (amp * c k i) * X i)) -
    C (μ.expect (fun ω => ∏ k, U ω k))

theorem wordShiftPolynomial_eval (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (c : K → V → ℝ)
    (amp : ℝ) (z : V → ℝ) :
    eval z (wordShiftPolynomial μ U c amp) =
      μ.expect (fun ω => ∏ k, (U ω k + ∑ i, amp * c k i * z i)) -
        μ.expect (fun ω => ∏ k, U ω k) := by
  simp only [wordShiftPolynomial, map_sub, map_sum, map_mul, map_prod, map_add, eval_C, eval_X,
    FiniteLaw.expect]

theorem wordShiftPolynomial_expansion (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (c : K → V → ℝ)
    (amp : ℝ) :
    wordShiftPolynomial μ U c amp = ∑ s : K → Option V,
      C (shiftChoiceWeight μ U s * amp ^ choiceDegree s * ∏ k : ShiftPositions s, c k.val (choiceSite s k)) *
        ∏ k : ShiftPositions s, X (choiceSite s k) := by
  apply MvPolynomial.funext
  intro z
  rw [wordShiftPolynomial_eval]
  simp only [map_sum, map_mul, map_prod, eval_C, eval_X]
  exact shift_increment_expansion μ U c amp z

theorem sitePatternFunctional_shift (w : Finset V → ℝ) (μ : FiniteLaw Ω)
    (U : Ω → K → ℝ) (c : K → V → ℝ) (amp : ℝ) :
    sitePatternFunctional w (wordShiftPolynomial μ U c amp) =
      ∑ s : K → Option V, if Function.Injective (choiceSite s) then
        (shiftChoiceWeight μ U s * amp ^ choiceDegree s *
          ∏ k : ShiftPositions s, c k.val (choiceSite s k)) * w (choiceSites s) else 0 := by
  rw [wordShiftPolynomial_expansion, map_sum]
  simp only [MvPolynomial.C_mul', map_smul, smul_eq_mul, sitePatternFunctional_prod_X,
    choiceSites, mul_ite, mul_zero]

end CausalLowerbound.PartC

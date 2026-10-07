import CausalLowerbound.PartB.IncidentFactorLedger
import Mathlib.Algebra.MvPolynomial.Eval

/-! The actual coefficient polynomials for the Lagrange construction.
Their coefficients are expanded into finite products of the elementary
graph multipliers; the negative constant coefficient is included. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

open ConfigurationShells MvPolynomial
variable {V E d : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype d] [DecidableEq d]

def atomDegree : Option (d × Bool) → (d × Bool →₀ ℕ) :=
  fun k => k.elim 0 (fun a => Finsupp.single a 1)

def atomSign : Option (d × Bool) → ℝ := fun k => k.elim (-1) (fun _ => 1)

def incidentOrientation (b : E → V) (i : V) (e : E) : Bool := decide (b e = i)

def lagrangeLinear (a b : E → V) (i : V) (e : {e : E // incident a b i e})
    (u : V × d → ℝ) : MvPolynomial (d × Bool) ℝ :=
  ∑ k : Option (d × Bool), monomial (atomDegree k)
    (atomSign k * graphFactor a b (e.val, incidentOrientation b i e.val, k) u)

def lagrangePolynomial (a b : E → V) (i : V) (u : V × d → ℝ) : MvPolynomial (d × Bool) ℝ :=
  ∏ e : {e : E // incident a b i e}, lagrangeLinear a b i e u

def lagrangeCoefficient (a b : E → V) (i : V) (ν : d × Bool →₀ ℕ) (u : V × d → ℝ) : ℝ :=
  coeff ν (lagrangePolynomial a b i u)

def selectionDegree {K : Type*} [Fintype K] (s : K → Option (d × Bool)) : d × Bool →₀ ℕ :=
  ∑ e, atomDegree (s e)

def selectionWeight {K : Type*} [Fintype K] (ν : d × Bool →₀ ℕ) (s : K → Option (d × Bool)) : ℝ :=
  if selectionDegree s = ν then ∏ e, atomSign (s e) else 0

theorem finite_prod_monomial {K α : Type*} (s : Finset K) (deg : K → α →₀ ℕ) (c : K → ℝ) :
    (∏ e ∈ s, monomial (deg e) (c e) : MvPolynomial α ℝ) = monomial (∑ e ∈ s, deg e) (∏ e ∈ s, c e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [← C_apply]
  | @insert i s hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih, monomial_mul]

theorem lagrange_polynomial_expansion (a b : E → V) (i : V) (u : V × d → ℝ) :
    lagrangePolynomial a b i u =
      ∑ s : {e : E // incident a b i e} → Option (d × Bool),
        monomial (selectionDegree s) (∏ e,
          atomSign (s e) * graphFactor a b (e.val, incidentOrientation b i e.val, s e) u) := by
  unfold lagrangePolynomial lagrangeLinear
  rw [Fintype.prod_sum (fun (e : {e : E // incident a b i e}) (k : Option (d × Bool)) =>
    monomial (atomDegree k) (atomSign k * graphFactor a b (e.val, incidentOrientation b i e.val, k) u))]
  apply Finset.sum_congr rfl
  intro s _
  exact finite_prod_monomial Finset.univ _ _

/-- Every actual Lagrange coefficient is a finite linear combination of
products containing exactly one elementary factor for each incident edge. -/
theorem lagrange_coefficient_expansion (a b : E → V) (i : V) (ν : d × Bool →₀ ℕ) (u : V × d → ℝ) :
    lagrangeCoefficient a b i ν u =
      ∑ s : {e : E // incident a b i e} → Option (d × Bool), selectionWeight ν s *
        ∏ e, graphFactor a b (e.val, incidentOrientation b i e.val, s e) u := by
  rw [lagrangeCoefficient, lagrange_polynomial_expansion, coeff_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [coeff_monomial, Finset.prod_mul_distrib]
  unfold selectionWeight
  split_ifs <;> simp_all only [mul_zero, zero_mul]

theorem lagrange_linear_eval (a b : E → V) (i : V) (e : {e : E // incident a b i e})
    (u : V × d → ℝ) (x : d × Bool → ℝ) :
    eval x (lagrangeLinear a b i e u) =
      -graphFactor a b (e.val, incidentOrientation b i e.val, none) u +
        ∑ k : d × Bool, graphFactor a b (e.val, incidentOrientation b i e.val, some k) u * x k := by
  simp [lagrangeLinear, Fintype.sum_option, atomDegree, atomSign, eval_monomial]

end CausalLowerbound.PartB.ShellGeometry

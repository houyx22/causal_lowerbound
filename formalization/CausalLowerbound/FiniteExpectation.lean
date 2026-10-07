import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite probability and expectation

The virtual signs in Part B have finite support. This small interface keeps the
first formalization independent of measure-theoretic integration.
-/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound

open scoped BigOperators

/-- A probability law on a finite sample space. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

/-- Expectation is an actual finite weighted sum. -/
def expect (f : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * f ω

theorem expect_congr {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) :
    μ.expect f = μ.expect g := by
  unfold expect
  apply Finset.sum_congr rfl
  intro ω _
  rw [h ω]

@[simp] theorem expect_const (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, μ.total, one_mul]

theorem expect_add (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω + g ω) = μ.expect f + μ.expect g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (f g : Ω → ℝ) :
    μ.expect (fun ω => f ω - g ω) = μ.expect f - μ.expect g := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul (c : ℝ) (f : Ω → ℝ) :
    μ.expect (fun ω => c * f ω) = c * μ.expect f := by
  simp only [expect, Finset.mul_sum, mul_left_comm]

theorem expect_mul_const (f : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => f ω * c) = μ.expect f * c := by
  simp only [expect, ← mul_assoc, Finset.sum_mul]

/-- Covariance for the same finite probability law. -/
def covariance (f g : Ω → ℝ) : ℝ :=
  μ.expect (fun ω => f ω * g ω) - μ.expect f * μ.expect g

/-- Independent product of two finite probability laws. -/
def prod {Γ : Type*} [Fintype Γ] (ν : FiniteLaw Γ) : FiniteLaw (Ω × Γ) where
  weight z := μ.weight z.1 * ν.weight z.2
  nonneg z := mul_nonneg (μ.nonneg z.1) (ν.nonneg z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ν.total, mul_one, μ.total]

theorem expect_prod {Γ : Type*} [Fintype Γ] (ν : FiniteLaw Γ) (f : Ω × Γ → ℝ) :
    (μ.prod ν).expect f = μ.expect (fun x => ν.expect (fun y => f (x, y))) := by
  simp only [expect, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expect_prod_mul {Γ : Type*} [Fintype Γ] (ν : FiniteLaw Γ)
    (f : Ω → ℝ) (g : Γ → ℝ) :
    (μ.prod ν).expect (fun z => f z.1 * g z.2) = μ.expect f * ν.expect g := by
  rw [μ.expect_prod]
  simp only [ν.expect_mul, μ.expect_mul_const]

/-- Independent laws on a finite family of possibly different sample spaces. -/
def independent {ι : Type*} [Fintype ι] [DecidableEq ι] {Ξ : ι → Type*}
    [∀ i, Fintype (Ξ i)] (laws : ∀ i, FiniteLaw (Ξ i)) :
    FiniteLaw (∀ i, Ξ i) := by
  classical
  refine { weight := fun ω => ∏ i, (laws i).weight (ω i)
           nonneg := fun ω => Finset.prod_nonneg (fun i _ => (laws i).nonneg (ω i))
           total := ?_ }
  rw [← Fintype.prod_sum]
  simp only [FiniteLaw.total, Finset.prod_const_one]

/-- Independence is derived from product weights, not assumed as an expectation axiom. -/
theorem expect_independent_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {Ξ : ι → Type*}
    [∀ i, Fintype (Ξ i)] (laws : ∀ i, FiniteLaw (Ξ i)) (f : ∀ i, Ξ i → ℝ) :
    (independent laws).expect (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (laws i).expect (f i) := by
  classical
  simp only [expect, independent, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i ω => (laws i).weight ω * f i ω)).symm

end FiniteLaw
end CausalLowerbound

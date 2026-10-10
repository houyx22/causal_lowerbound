import CausalLowerbound.UpperBound.InterpolationWeights
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! An explicit positive tensor grid and its nonsingular evaluation matrix.

Using coordinate degrees at most p gives (p+1)^d auxiliary nodes.  The anchor
and close partner are kept separately; the increased, fixed number of roles
does not enter the bandwidth exponents. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

section TensorMatrix

variable {d J : Type*} [Fintype d] [Fintype J] [DecidableEq J]

def tensorMatrix (A : d → Matrix J J ℝ) : Matrix (d → J) (d → J) ℝ :=
  fun u v => ∏ i, A i (u i) (v i)

omit [DecidableEq J] in
theorem tensorMatrix_mul (A B : d → Matrix J J ℝ) :
    tensorMatrix A * tensorMatrix B = tensorMatrix (fun i => A i * B i) := by
  classical
  ext u v
  simp only [Matrix.mul_apply, tensorMatrix]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j => A i (u i) j * B i j (v i))).symm

omit [Fintype J] in
theorem tensorMatrix_one : tensorMatrix (fun _ : d => (1 : Matrix J J ℝ)) = 1 := by
  classical
  ext u v
  by_cases huv : u = v
  · subst v
    simp [tensorMatrix]
  · rw [Matrix.one_apply_ne huv]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp huv
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

theorem tensorMatrix_isUnit_det (A : d → Matrix J J ℝ) (hA : ∀ i, IsUnit (A i).det) :
    IsUnit (tensorMatrix A).det := by
  classical
  apply Matrix.isUnit_det_of_right_inverse
    (B := tensorMatrix (fun i => (A i)⁻¹))
  rw [tensorMatrix_mul]
  simp only [Matrix.mul_nonsing_inv _ (hA _)]
  exact tensorMatrix_one

end TensorMatrix

/-- All grid coordinates lie strictly between zero and one. -/
def gridCoordinate (p : ℕ) (i : Fin (p + 1)) : ℝ := ((i : ℝ) + 1) / (p + 2)

theorem gridCoordinate_pos (p : ℕ) (i : Fin (p + 1)) : 0 < gridCoordinate p i := by
  unfold gridCoordinate
  positivity

theorem gridCoordinate_lt_one (p : ℕ) (i : Fin (p + 1)) : gridCoordinate p i < 1 := by
  unfold gridCoordinate
  apply (div_lt_one (by positivity : (0 : ℝ) < p + 2)).mpr
  have hi : (i : ℝ) < p + 1 := by exact_mod_cast i.isLt
  linarith

theorem gridCoordinate_injective (p : ℕ) : Function.Injective (gridCoordinate p) := by
  intro i j hij
  have hden : (p : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
  have hnum := (div_left_inj' hden).mp hij
  apply Fin.ext
  exact_mod_cast (add_right_cancel hnum)

variable {d : Type*} [Fintype d]

abbrev TensorIndex (d : Type*) (p : ℕ) := d → Fin (p + 1)

def gridNode (p : ℕ) (j : TensorIndex d p) : d → ℝ := fun i => gridCoordinate p (j i)

def tensorMonomial (p : ℕ) (ν : TensorIndex d p) (x : d → ℝ) : ℝ :=
  ∏ i, x i ^ (ν i : ℕ)

/-- Columns are observed auxiliary nodes and rows are monomials. -/
def tensorEvaluation (p : ℕ) (z : TensorIndex d p → d → ℝ) :
    Matrix (TensorIndex d p) (TensorIndex d p) ℝ :=
  fun ν j => tensorMonomial p ν (z j)

theorem tensorEvaluation_grid (p : ℕ) :
    tensorEvaluation p (gridNode (d := d) p) =
      tensorMatrix (fun _ : d => (Matrix.vandermonde (gridCoordinate p))ᵀ) := rfl

theorem tensorEvaluation_grid_isUnit_det (p : ℕ) :
    IsUnit (tensorEvaluation p (gridNode (d := d) p)).det := by
  classical
  rw [tensorEvaluation_grid]
  apply tensorMatrix_isUnit_det
  intro i
  apply Matrix.isUnit_det_transpose
  exact isUnit_iff_ne_zero.mpr
    (Matrix.det_vandermonde_ne_zero_iff.mpr (gridCoordinate_injective p))

theorem continuous_tensorMonomial (p : ℕ) (ν : TensorIndex d p) :
    Continuous (tensorMonomial p ν) := by
  unfold tensorMonomial
  fun_prop

theorem continuous_tensorEvaluation (p : ℕ) :
    Continuous (tensorEvaluation (d := d) p) := by
  unfold tensorEvaluation tensorMonomial
  fun_prop

end CausalLowerbound.UpperBound

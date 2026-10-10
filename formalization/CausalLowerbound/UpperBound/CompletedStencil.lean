import CausalLowerbound.UpperBound.UniformStencil

/-! A positive auxiliary tensor grid completes an anchor and a close partner.
The anchor coefficient is fixed at one before normalization; only the
auxiliary correction coefficients need to be solved for. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

variable {J : Type*} [Fintype J]

def completedCoefficients (c : J → ℝ) : Option J → ℝ := Option.elim' 1 c

/-- `none` is the partner, `some none` the anchor, and `some (some j)` an auxiliary node. -/
def completedStencil (c : J → ℝ) : Option (Option J) → ℝ :=
  normalizedStencil (completedCoefficients c)

theorem completedStencil_norm_sq (c : J → ℝ) : ∑ i, completedStencil c i ^ 2 = 1 :=
  normalizedStencil_norm_sq _

theorem completedStencil_anchor_pos (c : J → ℝ) : 0 < completedStencil c (some none) := by
  exact div_pos zero_lt_one (stencilNormalizer_pos _)

theorem completedStencil_partner_bound (c : J → ℝ) : |completedStencil c none| ≤ 1 :=
  normalizedStencil_partner_bound _

theorem completedStencil_auxiliary_bound (c : J → ℝ) (j : J) :
    |completedStencil c (some (some j))| ≤ |c j| :=
  normalizedStencil_coefficient_bound _ _

theorem completedStencil_cancel (c m : J → ℝ) (anchor partner : ℝ)
    (hm : ∑ j, c j * m j = partner - anchor) :
    completedStencil c (some none) * anchor + completedStencil c none * partner +
      ∑ j, completedStencil c (some (some j)) * m j = 0 := by
  have hm' : ∑ i : Option J, completedCoefficients c i * (Option.elim' anchor m) i = partner := by
    rw [Fintype.sum_option]
    simp only [completedCoefficients, Option.elim'_none, Option.elim'_some, one_mul, hm]
    ring
  have he := normalizedStencil_cancel (completedCoefficients c) (Option.elim' anchor m) partner hm'
  rw [Fintype.sum_option] at he
  simp only [Option.elim'_none, Option.elim'_some] at he
  change completedStencil c none * partner +
    (completedStencil c (some none) * anchor +
      ∑ j, completedStencil c (some (some j)) * m j) = 0 at he
  linarith

variable {d : Type*} [Fintype d]

/-- Each nonconstant monomial changes by at most η when all coordinates of
the close partner have absolute value at most η≤1. -/
theorem tensorMonomial_close_bound (p : ℕ) (ν : TensorIndex d p) (v : d → ℝ)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hv : ∀ i, |v i| ≤ η) :
    |tensorMonomial p ν v - tensorMonomial p ν 0| ≤ η := by
  by_cases hν : ∀ i, ν i = 0
  · simpa [tensorMonomial, hν] using hη
  · push_neg at hν
    obtain ⟨k, hk⟩ := hν
    have hk0 : (ν k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    have hzero : tensorMonomial p ν (0 : d → ℝ) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ k) (zero_pow hk0)
    have hkpow : |v k| ^ (ν k : ℕ) ≤ η := by
      calc
        _ = |v k| ^ ((ν k : ℕ) - 1) * |v k| := by
          rw [← pow_succ]
          congr 1
          omega
        _ ≤ 1 * η := mul_le_mul (pow_le_one₀ (abs_nonneg _) ((hv k).trans hη1))
          (hv k) (abs_nonneg _) zero_le_one
        _ = η := one_mul _
    rw [hzero, sub_zero, tensorMonomial, Finset.abs_prod]
    simp only [abs_pow]
    calc
      _ ≤ ∏ i : d, if i = k then η else 1 := by
        apply Finset.prod_le_prod (fun i _ => pow_nonneg (abs_nonneg _) _)
        intro i _
        by_cases hik : i = k
        · simpa only [hik, if_pos rfl] using hkpow
        · rw [if_neg hik]
          exact pow_le_one₀ (abs_nonneg _) ((hv i).trans hη1)
      _ = η := by simp

def tensorContrastCoefficients (p : ℕ) (z : TensorIndex d p → d → ℝ) (v : d → ℝ) :
    TensorIndex d p → ℝ :=
  interpolationCoefficients (tensorEvaluation p z)
    (fun ν => tensorMonomial p ν v - tensorMonomial p ν 0)

def tensorContrastWeights (p : ℕ) (z : TensorIndex d p → d → ℝ) (v : d → ℝ) :
    Option (Option (TensorIndex d p)) → ℝ := completedStencil (tensorContrastCoefficients p z v)

theorem tensorContrastWeights_cancel (p : ℕ) (z : TensorIndex d p → d → ℝ) (v : d → ℝ)
    (hz : IsUnit (tensorEvaluation p z).det) (ν : TensorIndex d p) :
    tensorContrastWeights p z v (some none) * tensorMonomial p ν 0 +
      tensorContrastWeights p z v none * tensorMonomial p ν v +
      ∑ j, tensorContrastWeights p z v (some (some j)) * tensorMonomial p ν (z j) = 0 := by
  apply completedStencil_cancel
  have he := congrFun (interpolationCoefficients_solve (tensorEvaluation p z)
    (fun ν => tensorMonomial p ν v - tensorMonomial p ν 0) hz) ν
  simpa only [Matrix.mulVec, dotProduct, tensorEvaluation, tensorContrastCoefficients,
    mul_comm] using he

theorem tensorContrastWeights_auxiliary_bound (p : ℕ)
    (z : TensorIndex d p → d → ℝ) (v : d → ℝ) {C η : ℝ}
    (hrow : ∀ i, ∑ j, |(tensorEvaluation p z)⁻¹ i j| ≤ C)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (hv : ∀ i, |v i| ≤ η) (j : TensorIndex d p) :
    |tensorContrastWeights p z v (some (some j))| ≤ C * η := by
  have he := interpolationCoefficients_perturbation (tensorEvaluation p z)
    (fun ν => tensorMonomial p ν v - tensorMonomial p ν 0) 0 hη hrow
    (fun ν => by simpa only [Pi.zero_apply, sub_zero] using tensorMonomial_close_bound p ν v hη hη1 hv) j
  simp only [interpolationCoefficients, Matrix.mulVec_zero, Pi.zero_apply, sub_zero] at he
  exact (completedStencil_auxiliary_bound (tensorContrastCoefficients p z v) j).trans he

end CausalLowerbound.UpperBound

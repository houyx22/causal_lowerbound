import CausalLowerbound.PeriodizedTorus

/-! Finite real linear combinations of concrete Wiener realizations. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.Wiener

variable {I α : Type*} [Fintype I] [Fintype α]

theorem finite_real_combination_wiener (w : I → ℝ) (f : I → (α → ℝ) → ℝ) (B : I → ℝ)
    (h : ∀ i, ∃ A : Fourier α, (∀ u, toContinuous A (torusProjection u) = (f i u : ℝ)) ∧ ‖A‖ ≤ B i) :
    ∃ A : Fourier α,
      (∀ u, toContinuous A (torusProjection u) = (∑ i, w i * f i u : ℝ)) ∧
      ‖A‖ ≤ ∑ i, |w i| * B i := by
  classical
  choose A hA hn using h
  refine ⟨∑ i, (w i : ℂ) • A i, ?_, ?_⟩
  · intro u
    simp only [map_sum, map_smul, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      hA, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  · calc
      ‖∑ i, (w i : ℂ) • A i‖ ≤ ∑ i, ‖(w i : ℂ) • A i‖ := norm_sum_le _ _
      _ = ∑ i, |w i| * ‖A i‖ := by simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ∑ i, |w i| * B i := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hn i) (abs_nonneg _))

end CausalLowerbound.Wiener

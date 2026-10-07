import CausalLowerbound.PartC.MixedLikelihoodPolynomials

/-! Uniform value bounds for the actual finite coefficient support.
The constants are independent of the active block set and the scale,
so the smallness condition in the pattern comparison is constructible. -/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry MvPolynomial
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω] [Inhabited Ω]

theorem exists_globalCarriedPolynomial_bound {Q : ℕ}
    (atoms : Ω → CoefficientExponent d Q → ℝ) :
    ∃ C > 0, ∀ (S : Finset (d → ℤ)) (U : S → Ω) (x₀ : d → ℝ) (r : ℝ), 0 < r →
      ∀ x, |eval (fun ka => atoms (U ka.1) ka.2) (globalCarriedPolynomial Q S x₀ r x)| ≤ C := by
  obtain ⟨C, hC, hc⟩ := carriedField_scale_control atoms 0
  refine ⟨C, hC, fun S U x₀ r hr x => ?_⟩
  rw [globalCarriedPolynomial_eval Q S atoms U x₀ r hr]
  have he := (hc S (extendBlockSample S U) x₀ r hr).bound 0 (by omega) x
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, mul_one] using he

theorem exists_paperCarried_small_amplitude (Q : ℕ) (ρ : ℝ) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ b : ℝ, 0 ≤ b → b ≤ ε →
      ∀ (S : Finset (d → ℤ)) (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q))
        (x₀ : d → ℝ) (r : ℝ), 0 < r → ∀ x,
        |b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
          (globalCarriedPolynomial Q S x₀ r x)| ≤ 1 := by
  obtain ⟨C, hC, hc⟩ := exists_globalCarriedPolynomial_bound (paperCoefficientAtoms (d := d) Q ρ)
  refine ⟨min 1 C⁻¹, lt_min (by norm_num) (inv_pos.mpr hC), min_le_left _ _, ?_⟩
  intro b hb hbe S ξ x₀ r hr x
  rw [abs_mul, abs_of_nonneg hb]
  calc
    _ ≤ b * C := mul_le_mul_of_nonneg_left (hc S ξ x₀ r hr x) hb
    _ ≤ C⁻¹ * C := mul_le_mul_of_nonneg_right (hbe.trans (min_le_right _ _)) hC.le
    _ = 1 := inv_mul_cancel₀ hC.ne'

end CausalLowerbound.PartC

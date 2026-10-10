import CausalLowerbound.UpperBound.PolynomialGram
import Mathlib.MeasureTheory.Integral.Prod

/-! A weight depending on the entire completed tuple retains the fixed
Gram lower bound.  No reduction to an anchor-only weight is assumed. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d B : Type*} [Fintype d] [MeasurableSpace B]

theorem weighted_tensorGram_lower (p : ℕ) (θ : TensorIndex d p → ℝ)
    (ν : Measure B) [IsFiniteMeasure ν] (W : (d → ℝ) × B → ℝ) (c : ℝ)
    (hW : ∀ᵐ z ∂(volume.restrict (anchorUnitBox d)).prod ν, c ≤ W z)
    (hI : Integrable (fun z => W z * tensorPolynomial p θ z.1 ^ 2)
      ((volume.restrict (anchorUnitBox d)).prod ν)) :
    c * ν.real univ * tensorGramEnergy p θ ≤
      ∫ z, W z * tensorPolynomial p θ z.1 ^ 2
        ∂(volume.restrict (anchorUnitBox d)).prod ν := by
  have hP : Integrable (fun x => tensorPolynomial p θ x ^ 2)
      (volume.restrict (anchorUnitBox d)) :=
    ((continuous_tensorPolynomial p θ).pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hbase : Integrable (fun z : (d → ℝ) × B => c * tensorPolynomial p θ z.1 ^ 2)
      ((volume.restrict (anchorUnitBox d)).prod ν) := by
    simpa only [mul_one] using (hP.const_mul c).mul_prod (integrable_const (1 : ℝ) (μ := ν))
  calc
    _ = ∫ z : (d → ℝ) × B, c * tensorPolynomial p θ z.1 ^ 2
        ∂(volume.restrict (anchorUnitBox d)).prod ν := by
      rw [integral_fun_fst (fun x => c * tensorPolynomial p θ x ^ 2),
        integral_const_mul, ← tensorGramEnergy_eq_integral]
      simp only [smul_eq_mul]
      ring
    _ ≤ _ := integral_mono_ae hbase hI (hW.mono
      (fun z hz => mul_le_mul_of_nonneg_right hz (sq_nonneg _)))

theorem exists_weighted_tensorGram_lower (p : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (θ : TensorIndex d p → ℝ)
      (ν : Measure B) (_ : IsFiniteMeasure ν) (W : (d → ℝ) × B → ℝ) (c : ℝ),
      0 ≤ c →
      (∀ᵐ z ∂(volume.restrict (anchorUnitBox d)).prod ν, c ≤ W z) →
      Integrable (fun z => W z * tensorPolynomial p θ z.1 ^ 2)
        ((volume.restrict (anchorUnitBox d)).prod ν) →
      c * ν.real univ * κ * ‖θ‖ ^ 2 ≤
        ∫ z, W z * tensorPolynomial p θ z.1 ^ 2
          ∂(volume.restrict (anchorUnitBox d)).prod ν := by
  obtain ⟨κ, hκ, hbound⟩ := exists_tensorGram_lower_bound (d := d) p
  refine ⟨κ, hκ, ?_⟩
  intro θ ν hν W c hc hW hI
  letI : IsFiniteMeasure ν := hν
  calc
    _ = (c * ν.real univ) * (κ * ‖θ‖ ^ 2) := by ring
    _ ≤ (c * ν.real univ) * tensorGramEnergy p θ :=
      mul_le_mul_of_nonneg_left (hbound θ) (mul_nonneg hc measureReal_nonneg)
    _ ≤ _ := weighted_tensorGram_lower p θ ν W c hW hI

end CausalLowerbound.UpperBound

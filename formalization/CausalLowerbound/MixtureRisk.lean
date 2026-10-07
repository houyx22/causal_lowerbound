import CausalLowerbound.DiscreteBayes

/-! A countable prior risk is bounded by a uniform risk bound, including
infinite risks and arbitrary nonnegative measurable losses. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators
namespace CausalLowerbound.DiscreteLaw
variable {I X : Type*} [MeasurableSpace X]

theorem lintegral_mixMeasures_le (π : DiscreteLaw I) (M : I → Measure X)
    (loss : X → ℝ≥0∞) (C : ℝ≥0∞) (h : ∀ i, (∫⁻ x, loss x ∂M i) ≤ C) :
    (∫⁻ x, loss x ∂π.mixMeasures M) ≤ C := by
  rw [mixMeasures, lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]
  calc
    _ ≤ ∑' i, ENNReal.ofReal (π.weight i) * C :=
      ENNReal.tsum_le_tsum (fun i => mul_le_mul_left' (h i) _)
    _ = C := by
      rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg π.nonneg π.summable_weight,
        π.tsum_weight, ENNReal.ofReal_one, one_mul]

end CausalLowerbound.DiscreteLaw

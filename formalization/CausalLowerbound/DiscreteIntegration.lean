import CausalLowerbound.DiscreteTilt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.NormedSpace.FunctionSeries

/-! Integration and continuity of a bounded countable mixture. These lemmas
retain the full carrier label space; no finite truncation is used. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
namespace CausalLowerbound.DiscreteLaw
variable {Ω X : Type*}

theorem abs_expect_le (μ : DiscreteLaw Ω) (f : Ω → ℝ) (B : ℝ)
    (hf : ∀ w, |f w| ≤ B) : |μ.expect f| ≤ B := by
  have hs := μ.summable_expect_of_bounded f B hf
  have hb : ∀ w, ‖μ.weight w * f w‖ ≤ μ.weight w * B := by
    intro w
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (μ.nonneg w)]
    exact mul_le_mul_of_nonneg_left (hf w) (μ.nonneg w)
  simpa only [one_mul, Real.norm_eq_abs] using
    hs.hasSum.norm_le_of_bounded (μ.total.mul_right B) hb

theorem expect_continuous [TopologicalSpace X] (μ : DiscreteLaw Ω)
    (f : Ω → X → ℝ) (B : ℝ) (hc : ∀ w, Continuous (f w))
    (hb : ∀ w x, |f w x| ≤ B) : Continuous (fun x => μ.expect (fun w => f w x)) := by
  apply continuous_tsum (fun w => continuous_const.mul (hc w))
    (μ.summable_weight.mul_right B)
  intro w x
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (μ.nonneg w)]
  exact mul_le_mul_of_nonneg_left (hb w x) (μ.nonneg w)

theorem integral_expect [Countable Ω] [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (μ : DiscreteLaw Ω) (f : Ω → X → ℝ) (B : ℝ)
    (hf : ∀ w, AEStronglyMeasurable (f w) ν) (hb : ∀ w x, |f w x| ≤ B) :
    (∫ x, μ.expect (fun w => f w x) ∂ν) = μ.expect (fun w => ∫ x, f w x ∂ν) := by
  have hi (w : Ω) : Integrable (f w) ν :=
    (integrable_const B).mono' (hf w) (Filter.Eventually.of_forall (hb w))
  have hwi (w : Ω) : Integrable (fun x => μ.weight w * f w x) ν := (hi w).const_mul _
  have hs : Summable (fun w => ∫ x, ‖μ.weight w * f w x‖ ∂ν) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      _ (μ.summable_weight.mul_right B)
    intro w
    calc
      _ ≤ ∫ _ : X, μ.weight w * B ∂ν := by
        apply integral_mono (hwi w).norm (integrable_const _)
        intro x
        change ‖μ.weight w * f w x‖ ≤ μ.weight w * B
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (μ.nonneg w)]
        exact mul_le_mul_of_nonneg_left (hb w x) (μ.nonneg w)
      _ = _ := by simp
  change (∫ x, ∑' w, μ.weight w * f w x ∂ν) = _
  rw [← integral_tsum_of_summable_integral_norm hwi hs]
  simp only [integral_const_mul, expect]

end CausalLowerbound.DiscreteLaw

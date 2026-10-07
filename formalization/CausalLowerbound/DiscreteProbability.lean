import CausalLowerbound.DiscreteLaw
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Constructions.Pi

/-! The countable carrier laws as genuine probability measures, including
finite independent products. No truncation of the label space is made. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalLowerbound
namespace DiscreteLaw
variable {Ω : Type*}

def toPMF (μ : DiscreteLaw Ω) : PMF Ω :=
  ⟨fun x => ENNReal.ofReal (μ.weight x), by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [← ENNReal.ofReal_tsum_of_nonneg μ.nonneg μ.summable_weight, μ.tsum_weight, ENNReal.ofReal_one]⟩

@[simp] theorem toPMF_apply (μ : DiscreteLaw Ω) (x : Ω) : μ.toPMF x = ENNReal.ofReal (μ.weight x) := rfl

def ofPMF (p : PMF Ω) : DiscreteLaw Ω where
  weight x := (p x).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    have hs : Summable (fun x => (p x).toReal) := ENNReal.summable_toReal p.tsum_coe_ne_top
    apply hs.hasSum_iff.mpr
    rw [← ENNReal.tsum_toReal_eq (fun x => p.apply_ne_top x), p.tsum_coe, ENNReal.toReal_one]

def toMeasure [MeasurableSpace Ω] (μ : DiscreteLaw Ω) : Measure Ω := μ.toPMF.toMeasure
instance [MeasurableSpace Ω] (μ : DiscreteLaw Ω) : IsProbabilityMeasure μ.toMeasure :=
  inferInstanceAs (IsProbabilityMeasure μ.toPMF.toMeasure)

theorem integral_eq_expect [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : DiscreteLaw Ω) (f : Ω → ℝ) (hf : Integrable f μ.toMeasure) :
    (∫ x, f x ∂μ.toMeasure) = μ.expect f := by
  rw [toMeasure, PMF.integral_eq_tsum _ f hf]
  simp only [expect, toPMF_apply, ENNReal.toReal_ofReal (μ.nonneg _), smul_eq_mul]

def independent {K : Type*} [Fintype K] (μ : K → DiscreteLaw ℕ) : DiscreteLaw (K → ℕ) :=
  ofPMF ((Measure.pi (fun k => (μ k).toMeasure)).toPMF)

theorem independent_weight {K : Type*} [Fintype K] (μ : K → DiscreteLaw ℕ) (x : K → ℕ) :
    (independent μ).weight x = ∏ k, (μ k).weight (x k) := by
  classical
  change ((Measure.pi (fun k => (μ k).toMeasure)).toPMF x).toReal = _
  rw [Measure.toPMF_apply, ← Set.univ_pi_singleton x, Measure.pi_pi]
  simp only [toMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    ENNReal.toReal_prod, toPMF_apply, ENNReal.toReal_ofReal (DiscreteLaw.nonneg _ _)]

end DiscreteLaw
end CausalLowerbound

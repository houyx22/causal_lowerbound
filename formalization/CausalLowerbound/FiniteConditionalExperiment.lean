import CausalLowerbound.DiscreteProbability
import Mathlib.MeasureTheory.Measure.WithDensity

/-! A continuous covariate law with a measurable finite conditional law. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalLowerbound
variable {X A : Type*} [MeasurableSpace X] [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

def conditionalExperiment (μ : Measure X) (K : X → FiniteLaw A) : Measure (X × A) :=
  (μ.prod Measure.count).withDensity (fun z => ENNReal.ofReal ((K z.1).weight z.2))

theorem conditionalWeight_measurable (K : X → FiniteLaw A)
    (hK : ∀ a, Measurable (fun x => (K x).weight a)) :
    Measurable (fun z : X × A => ENNReal.ofReal ((K z.1).weight z.2)) :=
  measurable_from_prod_countable (fun a => (hK a).ennreal_ofReal)

theorem conditionalWeight_total (K : FiniteLaw A) :
    (∑ a, ENNReal.ofReal (K.weight a)) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => K.nonneg a), K.total, ENNReal.ofReal_one]

theorem conditionalExperiment_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (K : X → FiniteLaw A) (hK : ∀ a, Measurable (fun x => (K x).weight a)) :
    IsProbabilityMeasure (conditionalExperiment μ K) := by
  constructor
  rw [conditionalExperiment, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_prod _ (conditionalWeight_measurable K hK).aemeasurable]
  simp only [lintegral_count, tsum_fintype, conditionalWeight_total, lintegral_const,
    measure_univ, mul_one]

theorem conditionalExperiment_covariate (μ : Measure X) [SFinite μ] (K : X → FiniteLaw A)
    (hK : ∀ a, Measurable (fun x => (K x).weight a)) :
    (conditionalExperiment μ K).map Prod.fst = μ := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, conditionalExperiment,
    withDensity_apply _ (measurable_fst hs)]
  have he : Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set A) := by ext z; simp
  rw [he, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod _ (conditionalWeight_measurable K hK).aemeasurable]
  simp only [lintegral_count, tsum_fintype, conditionalWeight_total, lintegral_const,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul]

theorem conditionalExperiment_density (μ : Measure X) (f : X → ℝ) (hf : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (K : X → FiniteLaw A)
    (hK : ∀ a, Measurable (fun x => (K x).weight a)) :
    conditionalExperiment (μ.withDensity (fun x => ENNReal.ofReal (f x))) K =
      (μ.prod Measure.count).withDensity (fun z => ENNReal.ofReal (f z.1 * (K z.1).weight z.2)) := by
  have hm : Measurable (fun z : X × A => ENNReal.ofReal (f z.1)) := hf.ennreal_ofReal.comp measurable_fst
  rw [conditionalExperiment, prod_withDensity_left hf.ennreal_ofReal,
    ← withDensity_mul (μ.prod Measure.count) hm (conditionalWeight_measurable K hK)]
  congr 1
  funext z
  exact (ENNReal.ofReal_mul (hn z.1)).symm
end CausalLowerbound

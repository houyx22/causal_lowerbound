import CausalLowerbound.FiniteProductDensities
import CausalLowerbound.FiniteConditionalExperiment

/-! Bayes' formula identifies the conditional representation with the
original countable mixture of sampling experiments. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound
variable {I X Y : Type*} [Countable I] [MeasurableSpace X] [Fintype Y]
  [MeasurableSpace Y] [MeasurableSingletonClass Y]

theorem DiscreteLaw.conditional_mixture (π : DiscreteLaw I) (μ : Measure X)
    (f : I → X → ℝ) (B : ℝ) (hf : ∀ i, Measurable (f i))
    (hn : ∀ i x, 0 ≤ f i x) (hb : ∀ i x, f i x ≤ B)
    (L : I → X → FiniteLaw Y) (hL : ∀ i y, Measurable (fun x => (L i x).weight y))
    (K : X → FiniteLaw Y) (hK : ∀ y, Measurable (fun x => (K x).weight y))
    (hden : ∀ x, 0 < π.expect (fun i => f i x))
    (hBayes : ∀ x y, (K x).weight y =
      π.expect (fun i => f i x * (L i x).weight y) / π.expect (fun i => f i x)) :
    conditionalExperiment (π.mixMeasures (fun i => μ.withDensity (fun x => ENNReal.ofReal (f i x)))) K =
      π.mixMeasures (fun i => conditionalExperiment (μ.withDensity (fun x => ENNReal.ofReal (f i x))) (L i)) := by
  have hfm : Measurable (fun x => π.expect (fun i => f i x)) := by
    apply measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset I))
      (fun s => Finset.measurable_sum s (fun i _ => measurable_const.mul (hf i)))
    exact tendsto_pi_nhds.mpr (fun x => (π.summable_expect_of_bounded _ B
      (fun i => by rw [abs_of_nonneg (hn i x)]; exact hb i x)).hasSum)
  rw [π.mixMeasures_withDensity μ f B hf hn hb,
    conditionalExperiment_density μ _ hfm (fun x => (hden x).le) K hK]
  have hr (i) := conditionalExperiment_density μ (f i) (hf i) (hn i) (L i) (hL i)
  simp_rw [hr]
  rw [π.mixMeasures_withDensity (μ.prod Measure.count)
    (fun i z => f i z.1 * (L i z.1).weight z.2) B
    (fun i => ((hf i).comp measurable_fst).mul (measurable_from_prod_countable (hL i)))
    (fun i z => mul_nonneg (hn i z.1) ((L i z.1).nonneg z.2))
    (fun i z => (mul_le_of_le_one_right (hn i z.1) ((L i z.1).weight_le_one z.2)).trans (hb i z.1))]
  congr 1
  funext z
  congr 1
  rw [hBayes]
  exact mul_div_cancel₀ _ (hden z.1).ne'

end CausalLowerbound

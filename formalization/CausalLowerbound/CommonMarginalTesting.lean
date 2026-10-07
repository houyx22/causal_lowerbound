import CausalLowerbound.DensityTesting
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! The component principle on a continuous covariate space. The distance
is the L1 distance of the actual joint densities relative to μ × counting
measure, and the exceptional event is charged only once. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound
variable {X A : Type*} [MeasurableSpace X] [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

theorem conditionalRealWeight_measurable (P : X → FiniteLaw A)
    (hP : ∀ a, Measurable (fun x => (P x).weight a)) :
    Measurable (fun z : X × A => (P z.1).weight z.2) := measurable_from_prod_countable hP

theorem conditionalRealWeight_integrable (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → FiniteLaw A) (hP : ∀ a, Measurable (fun x => (P x).weight a)) :
    Integrable (fun z : X × A => (P z.1).weight z.2) (μ.prod Measure.count) := by
  apply (integrable_const (1 : ℝ)).mono' (conditionalRealWeight_measurable P hP).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg ((P z.1).nonneg z.2)]
  exact (P z.1).weight_le_one z.2

def conditionalDensityLaw (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → FiniteLaw A) (hP : ∀ a, Measurable (fun x => (P x).weight a)) :
    DensityLaw (μ.prod (Measure.count : Measure A)) where
  density z := (P z.1).weight z.2
  nonneg z := (P z.1).nonneg z.2
  measurable := conditionalRealWeight_measurable P hP
  integrable := conditionalRealWeight_integrable μ P hP
  total := by
    rw [integral_prod _ (conditionalRealWeight_integrable μ P hP)]
    simp only [integral_count, FiniteLaw.total, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]

theorem conditionalDensityLaw_toMeasure (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → FiniteLaw A) (hP : ∀ a, Measurable (fun x => (P x).weight a)) :
    (conditionalDensityLaw μ P hP).toMeasure = conditionalExperiment μ P := rfl

theorem conditionalTV_measurable (P Q : X → FiniteLaw A)
    (hP : ∀ a, Measurable (fun x => (P x).weight a))
    (hQ : ∀ a, Measurable (fun x => (Q x).weight a)) :
    Measurable (fun x => (P x).totalVariation (Q x)) := by
  exact (Finset.measurable_sum _ (fun a _ => continuous_abs.measurable.comp ((hP a).sub (hQ a)))).div_const 2

theorem conditionalTV_integrable (μ : Measure X) [IsProbabilityMeasure μ]
    (P Q : X → FiniteLaw A) (hP : ∀ a, Measurable (fun x => (P x).weight a))
    (hQ : ∀ a, Measurable (fun x => (Q x).weight a)) :
    Integrable (fun x => (P x).totalVariation (Q x)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (conditionalTV_measurable P Q hP hQ).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (FiniteLaw.totalVariation_nonneg _ _)]
  exact FiniteLaw.totalVariation_le_one _ _

theorem common_marginal_totalVariation (μ : Measure X) [IsProbabilityMeasure μ]
    (P Q : X → FiniteLaw A) (hP : ∀ a, Measurable (fun x => (P x).weight a))
    (hQ : ∀ a, Measurable (fun x => (Q x).weight a)) :
    (conditionalDensityLaw μ P hP).totalVariation (conditionalDensityLaw μ Q hQ) =
      ∫ x, (P x).totalVariation (Q x) ∂μ := by
  have hi : Integrable (fun z : X × A => |(P z.1).weight z.2 - (Q z.1).weight z.2|) (μ.prod Measure.count) :=
    ((conditionalRealWeight_integrable μ P hP).sub (conditionalRealWeight_integrable μ Q hQ)).abs
  change (∫ z : X × A, |(P z.1).weight z.2 - (Q z.1).weight z.2| ∂μ.prod Measure.count) / 2 = _
  rw [integral_prod _ hi]
  simp only [integral_count, FiniteLaw.totalVariation, integral_div]

/-- Jensen's inequality for the square, proved directly by nonnegative variance. -/
theorem square_integral_le_integral_square (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℝ) (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  let m := ∫ x, f x ∂μ
  have he : (∫ x, (f x - m) ^ 2 ∂μ) = (∫ x, f x ^ 2 ∂μ) - 2 * m * m + m ^ 2 := by
    have he (x : X) : (f x - m) ^ 2 = (f x ^ 2 - (2 * m) * f x) + m ^ 2 := by ring
    have hlin : Integrable (fun x => (2 * m) * f x) μ := hf.const_mul _
    have hsub : Integrable (fun x => f x ^ 2 - (2 * m) * f x) μ := hf2.sub hlin
    simp_rw [he]
    rw [integral_add hsub (integrable_const _), integral_sub hf2 hlin, integral_const_mul]
    simp [m]
  have hn := integral_nonneg (μ := μ) (fun x : X => sq_nonneg (f x - m))
  rw [he] at hn
  dsimp [m] at hn
  nlinarith

theorem common_marginal_component_principle (μ : Measure X) [IsProbabilityMeasure μ]
    (P Q : X → FiniteLaw A) (hP : ∀ a, Measurable (fun x => (P x).weight a))
    (hQ : ∀ a, Measurable (fun x => (Q x).weight a))
    (bad : Set X) (hb : MeasurableSet bad) (cost : X → ℝ) (hc : Integrable cost μ)
    (hlow : ∀ x, x ∉ bad → (P x).hellingerSq (Q x) ≤ cost x) :
    (conditionalDensityLaw μ P hP).totalVariation (conditionalDensityLaw μ Q hQ) ≤
      μ.real bad + Real.sqrt (∫ x, badᶜ.indicator cost x ∂μ) := by
  let v := fun x => (P x).totalVariation (Q x)
  let g := badᶜ.indicator v
  have hv : Integrable v μ := conditionalTV_integrable μ P Q hP hQ
  have hg : Integrable g μ := hv.indicator hb.compl
  have hg0 (x : X) : 0 ≤ g x := by
    by_cases hx : x ∈ bad <;> simp [g, Set.indicator, hx, v, FiniteLaw.totalVariation_nonneg]
  have hg1 (x : X) : g x ≤ 1 := by
    by_cases hx : x ∈ bad <;> simp [g, Set.indicator, hx, v, FiniteLaw.totalVariation_le_one]
  have hg2 : Integrable (fun x => g x ^ 2) μ := by
    apply (integrable_const (1 : ℝ)).mono' (hg.aestronglyMeasurable.pow 2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change g x ^ 2 ≤ 1
    nlinarith [hg0 x, hg1 x]
  have hsq : (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, badᶜ.indicator cost x ∂μ := by
    apply (square_integral_le_integral_square μ g hg hg2).trans
    apply integral_mono hg2 (hc.indicator hb.compl)
    intro x
    by_cases hx : x ∈ bad
    · simp [g, Set.indicator, hx]
    · simpa [g, Set.indicator, hx, v] using
        (FiniteLaw.totalVariation_sq_le_hellingerSq (P x) (Q x)).trans (hlow x hx)
  have hgood := Real.le_sqrt_of_sq_le hsq
  have hbad : (∫ x, bad.indicator v x ∂μ) ≤ μ.real bad := by
    calc
      _ ≤ ∫ x, bad.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        apply integral_mono (hv.indicator hb) ((integrable_const _).indicator hb)
        intro x
        by_cases hx : x ∈ bad
        · simp only [Set.indicator_of_mem hx]
          exact FiniteLaw.totalVariation_le_one _ _
        · simp only [Set.indicator_of_not_mem hx]
          exact le_rfl
      _ = _ := integral_indicator_one hb
  have hsplit : v = fun x => bad.indicator v x + g x := by
    funext x
    by_cases hx : x ∈ bad <;> simp [g, Set.indicator, hx]
  rw [common_marginal_totalVariation μ P Q hP hQ]
  change (∫ x, v x ∂μ) ≤ _
  calc
    _ = (∫ x, bad.indicator v x ∂μ) + ∫ x, g x ∂μ := by
      conv_lhs => rw [hsplit]
      exact integral_add (hv.indicator hb) hg
    _ ≤ _ := add_le_add hbad hgood

/-- The component estimate feeds the genuine continuous-sample two-point
bound. Instantiating cost with the paper's geometric estimate is separate. -/
theorem component_two_point_lower_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (P Q : X → FiniteLaw A) (hP : ∀ a, Measurable (fun x => (P x).weight a))
    (hQ : ∀ a, Measurable (fun x => (Q x).weight a))
    (bad : Set X) (hb : MeasurableSet bad) (cost : X → ℝ) (hc : Integrable cost μ)
    (hlow : ∀ x, x ∉ bad → (P x).hellingerSq (Q x) ≤ cost x)
    (hsmall : μ.real bad + Real.sqrt (∫ x, badᶜ.indicator cost x ∂μ) ≤ 1 / 2)
    (est : X × A → ℝ) (he : Measurable est) (θ₀ θ₁ : ℝ) (hθ : θ₀ ≤ θ₁) :
    ENNReal.ofReal ((θ₁ - θ₀) / 4) ≤
      max (∫⁻ z, ENNReal.ofReal |est z - θ₁| ∂conditionalExperiment μ P)
          (∫⁻ z, ENNReal.ofReal |est z - θ₀| ∂conditionalExperiment μ Q) := by
  exact DensityLaw.two_point_quarter (conditionalDensityLaw μ P hP) (conditionalDensityLaw μ Q hQ)
    est he θ₀ θ₁ hθ ((common_marginal_component_principle μ P Q hP hQ bad hb cost hc hlow).trans hsmall)

theorem component_bound_tendsto {Y W : ℕ → Type*}
    [∀ n, MeasurableSpace (Y n)] [∀ n, Fintype (W n)]
    [∀ n, MeasurableSpace (W n)] [∀ n, MeasurableSingletonClass (W n)]
    (μ : ∀ n, Measure (Y n)) [∀ n, IsProbabilityMeasure (μ n)]
    (P Q : ∀ n, Y n → FiniteLaw (W n))
    (hP : ∀ n a, Measurable (fun x => (P n x).weight a))
    (hQ : ∀ n a, Measurable (fun x => (Q n x).weight a))
    (bad : ∀ n, Set (Y n)) (hb : ∀ n, MeasurableSet (bad n)) (cost : ∀ n, Y n → ℝ)
    (hc : ∀ n, Integrable (cost n) (μ n))
    (hlow : ∀ n x, x ∉ bad n → (P n x).hellingerSq (Q n x) ≤ cost n x)
    (hbad : Filter.Tendsto (fun n => (μ n).real (bad n)) Filter.atTop (nhds 0))
    (hcost : Filter.Tendsto (fun n => ∫ x, (bad n)ᶜ.indicator (cost n) x ∂μ n) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => (conditionalDensityLaw (μ n) (P n) (hP n)).totalVariation
      (conditionalDensityLaw (μ n) (Q n) (hQ n))) Filter.atTop (nhds 0) := by
  have hs := hbad.add ((Real.continuous_sqrt.tendsto 0).comp hcost)
  apply squeeze_zero (fun n => DensityLaw.totalVariation_nonneg _ _)
    (fun n => common_marginal_component_principle (μ n) (P n) (Q n) (hP n) (hQ n)
      (bad n) (hb n) (cost n) (hc n) (hlow n))
  simpa only [Real.sqrt_zero, add_zero] using hs

end CausalLowerbound

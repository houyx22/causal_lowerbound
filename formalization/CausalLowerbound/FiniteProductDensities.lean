import CausalLowerbound.FiniteProductMeasures
import Mathlib.MeasureTheory.Integral.Pi

/-! Finite product densities and countable mixtures, as identities of measures. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical ENNReal
namespace CausalLowerbound
variable {I X A : Type*} [Fintype I] [MeasurableSpace X]

theorem finiteProduct_withDensity (μ : I → Measure X) [∀ i, SigmaFinite (μ i)]
    (f : I → X → ℝ) (hf : ∀ i, Integrable (f i) (μ i)) (hn : ∀ i x, 0 ≤ f i x)
    [∀ i, SigmaFinite ((μ i).withDensity (fun x => ENNReal.ofReal (f i x)))] :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hip := @Integrable.fintype_prod_dep ℝ inferInstance I inferInstance (fun _ => X) f
    (fun i => { volume := (μ i).restrict (s i) })
    (fun i => inferInstanceAs (SigmaFinite ((μ i).restrict (s i))))
    (fun i => (hf i).restrict)
  change Integrable (fun x : I → X => ∏ i, f i (x i)) (Measure.pi (fun i => (μ i).restrict (s i))) at hip
  rw [← ofReal_integral_eq_lintegral_ofReal hip
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hn i (x i))))]
  have he := @integral_fintype_prod_eq_prod ℝ inferInstance I inferInstance (fun _ => X) f
    (fun i => { volume := (μ i).restrict (s i) })
    (fun i => inferInstanceAs (SigmaFinite ((μ i).restrict (s i))))
  change (∫ x : I → X, ∏ i, f i (x i) ∂Measure.pi (fun i => (μ i).restrict (s i))) =
    ∏ i, ∫ x, f i x ∂(μ i).restrict (s i) at he
  rw [he, ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hn i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i),
    ofReal_integral_eq_lintegral_ofReal (hf i).restrict (Filter.Eventually.of_forall (hn i))]

theorem DiscreteLaw.mixMeasures_withDensity [Countable A] (π : DiscreteLaw A) (μ : Measure X)
    (f : A → X → ℝ) (B : ℝ) (hf : ∀ a, Measurable (f a))
    (hn : ∀ a x, 0 ≤ f a x) (hb : ∀ a x, f a x ≤ B) :
    π.mixMeasures (fun a => μ.withDensity (fun x => ENNReal.ofReal (f a x))) =
      μ.withDensity (fun x => ENNReal.ofReal (π.expect (fun a => f a x))) := by
  have he (x) : ENNReal.ofReal (π.expect (fun a => f a x)) =
      ∑' a, ENNReal.ofReal (π.weight a) * ENNReal.ofReal (f a x) := by
    rw [DiscreteLaw.expect, ENNReal.ofReal_tsum_of_nonneg (fun a => mul_nonneg (π.nonneg a) (hn a x))
      (π.summable_expect_of_bounded _ B (fun a => by rw [abs_of_nonneg (hn a x)]; exact hb a x))]
    apply tsum_congr
    intro a
    exact ENNReal.ofReal_mul (π.nonneg a)
  have hfun : (fun x => ENNReal.ofReal (π.expect (fun a => f a x))) =
      ∑' a, (fun x => ENNReal.ofReal (π.weight a) * ENNReal.ofReal (f a x)) := by
    funext x
    rw [tsum_apply (Pi.summable.mpr (fun _ => ENNReal.summable))]
    exact he x
  rw [hfun, withDensity_tsum (fun a => measurable_const.mul (hf a).ennreal_ofReal)]
  unfold DiscreteLaw.mixMeasures
  congr 1
  funext a
  exact (withDensity_smul (μ := μ) (ENNReal.ofReal (π.weight a)) (hf a).ennreal_ofReal).symm

end CausalLowerbound

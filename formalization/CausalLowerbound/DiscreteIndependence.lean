import CausalLowerbound.DiscreteIntegration
import Mathlib.MeasureTheory.Integral.Pi

/-! Factorization of bounded expectations under the actual countable
product law. This supplies independence at the level of probabilities. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MeasureTheory
namespace CausalLowerbound.DiscreteLaw
variable {K : Type*} [Fintype K]

theorem ofPMF_toPMF {Ω : Type*} (p : PMF Ω) : (ofPMF p).toPMF = p := by
  apply PMF.ext
  intro x
  exact ENNReal.ofReal_toReal (p.apply_ne_top x)

theorem independent_toMeasure (μ : K → DiscreteLaw ℕ) :
    (independent μ).toMeasure = Measure.pi (fun k => (μ k).toMeasure) := by
  rw [independent, toMeasure, ofPMF_toPMF, Measure.toPMF_toMeasure]

theorem integrable_bounded {Ω : Type*} [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : DiscreteLaw Ω) (f : Ω → ℝ) (B : ℝ) (hb : ∀ x, |f x| ≤ B) : Integrable f μ.toMeasure :=
  (integrable_const B).mono' (measurable_of_countable f).aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

theorem expect_independent_prod (μ : K → DiscreteLaw ℕ) (f : K → ℕ → ℝ)
    (B : K → ℝ) (hb : ∀ k x, |f k x| ≤ B k) :
    (independent μ).expect (fun x => ∏ k, f k (x k)) = ∏ k, (μ k).expect (f k) := by
  have hprod (x : K → ℕ) : |∏ k, f k (x k)| ≤ ∏ k, B k := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun k _ => hb k (x k))
  rw [← integral_eq_expect _ _ (integrable_bounded (independent μ) _ _ hprod), independent_toMeasure]
  have he := @integral_fintype_prod_eq_prod ℝ inferInstance K inferInstance (fun _ => ℕ) f
    (fun k => ⟨(μ k).toMeasure⟩) (fun k => inferInstanceAs (SigmaFinite (μ k).toMeasure))
  change (∫ x, ∏ k, f k (x k) ∂Measure.pi (fun k => (μ k).toMeasure)) =
    ∏ k, ∫ x, f k x ∂(μ k).toMeasure at he
  rw [he]
  apply Finset.prod_congr rfl
  intro k _
  exact integral_eq_expect _ _ (integrable_bounded (μ k) (f k) (B k) (hb k))

end CausalLowerbound.DiscreteLaw

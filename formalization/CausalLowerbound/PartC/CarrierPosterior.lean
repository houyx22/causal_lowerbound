import CausalLowerbound.PartC.CarrierSampleDensity
import CausalLowerbound.DiscreteBayes
import CausalLowerbound.DiscreteMixture
import CausalLowerbound.PartB.ConditionalMeasurability

/-! The full countable posterior conditional on the actual covariates.
This posterior retains shared signs; no block or sign independence is
asserted after conditioning. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {d I A : Type*} [Fintype d] [DecidableEq d] [Fintype A] {θ : ℝ}

def carrierPosterior (π : DiscreteLaw I) (F : I → CarrierProfile d θ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) : DiscreteLaw I :=
  π.tilt (fun z => (F z).sampleDensity S x₀ r x)
    (((1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d)) ^ n)
    (((1 + θ) ^ (5 ^ Fintype.card d) / (1 - θ) ^ (5 ^ Fintype.card d)) ^ n)
    (pow_pos (div_pos (pow_pos (sub_pos.mpr hθ1) _) (pow_pos (by linarith) _)) n)
    (fun z => (F z).sampleDensity_bounds hθ hθ1 S x₀ r x)

def carrierPosteriorConditional (π : DiscreteLaw I) (F : I → CarrierProfile d θ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (r : ℝ) {n : ℕ} (L : I → (Fin n → d → ℝ) → FiniteLaw A)
    (x : Fin n → d → ℝ) : FiniteLaw A :=
  (carrierPosterior π F hθ hθ1 S x₀ r x).mixFinite (fun z => L z x)

theorem carrierPosteriorConditional_weight (π : DiscreteLaw I) (F : I → CarrierProfile d θ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (r : ℝ) {n : ℕ} (L : I → (Fin n → d → ℝ) → FiniteLaw A)
    (x : Fin n → d → ℝ) (y : A) :
    (carrierPosteriorConditional π F hθ hθ1 S x₀ r L x).weight y =
      π.expect (fun z => (F z).sampleDensity S x₀ r x * (L z x).weight y) /
        π.expect (fun z => (F z).sampleDensity S x₀ r x) := by
  change (carrierPosterior π F hθ hθ1 S x₀ r x).expect (fun z => (L z x).weight y) = _
  rw [carrierPosterior, DiscreteLaw.tilt_expect]
  ring

theorem carrierSampleMarginal_pos (π : DiscreteLaw I) (F : I → CarrierProfile d θ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) :
    0 < π.expect (fun z => (F z).sampleDensity S x₀ r x) := by
  have hlo : 0 < ((1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d)) ^ n :=
    pow_pos (div_pos (pow_pos (sub_pos.mpr hθ1) _) (pow_pos (by linarith) _)) n
  exact hlo.trans_le (π.expect_bounds _ _ _ hlo.le
    (fun z => (F z).sampleDensity_bounds hθ hθ1 S x₀ r x)).1

theorem carrierPosteriorConditional_measurable [Countable I]
    (π : DiscreteLaw I) (F : I → CarrierProfile d θ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (r : ℝ) {n : ℕ} (L : I → (Fin n → d → ℝ) → FiniteLaw A)
    (hL : ∀ z y, Measurable (fun x => (L z x).weight y)) (y : A) :
    Measurable (fun x => (carrierPosteriorConditional π F hθ hθ1 S x₀ r L x).weight y) := by
  simp only [carrierPosteriorConditional_weight]
  apply Measurable.div
  · apply π.expect_measurable _ (((1 + θ) ^ (5 ^ Fintype.card d) /
      (1 - θ) ^ (5 ^ Fintype.card d)) ^ n)
      (fun z => ((F z).sampleDensity_measurable hθ hθ1 S x₀ r n).mul (hL z y))
    intro z x
    rw [abs_of_nonneg (mul_nonneg ((F z).sampleDensity_pos hθ hθ1 S x₀ r x).le ((L z x).nonneg y))]
    exact (mul_le_of_le_one_right ((F z).sampleDensity_pos hθ hθ1 S x₀ r x).le
      ((L z x).weight_le_one y)).trans ((F z).sampleDensity_bounds hθ hθ1 S x₀ r x).2
  · apply π.expect_measurable _ (((1 + θ) ^ (5 ^ Fintype.card d) /
      (1 - θ) ^ (5 ^ Fintype.card d)) ^ n)
      (fun z => (F z).sampleDensity_measurable hθ hθ1 S x₀ r n)
    intro z x
    rw [abs_of_pos ((F z).sampleDensity_pos hθ hθ1 S x₀ r x)]
    exact ((F z).sampleDensity_bounds hθ hθ1 S x₀ r x).2

theorem carrierPosteriorConditional_eq_mixture [Countable I]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (π : DiscreteLaw I) (F : I → CarrierProfile d θ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (r : ℝ) {n : ℕ} (L : I → (Fin n → d → ℝ) → FiniteLaw A)
    (hL : ∀ z y, Measurable (fun x => (L z x).weight y)) :
    conditionalExperiment (π.mixMeasures (fun z => (F z).sampleMeasure S x₀ r n))
      (carrierPosteriorConditional π F hθ hθ1 S x₀ r L) =
      π.mixMeasures (fun z => conditionalExperiment ((F z).sampleMeasure S x₀ r n) (L z)) := by
  simp_rw [CarrierProfile.sampleMeasure_density _ hθ hθ1]
  apply π.conditional_mixture (Measure.pi (fun _ : Fin n => cubeMeasure d))
    (fun z x => (F z).sampleDensity S x₀ r x)
    (((1 + θ) ^ (5 ^ Fintype.card d) / (1 - θ) ^ (5 ^ Fintype.card d)) ^ n)
    (fun z => (F z).sampleDensity_measurable hθ hθ1 S x₀ r n)
    (fun z x => ((F z).sampleDensity_pos hθ hθ1 S x₀ r x).le)
    (fun z x => ((F z).sampleDensity_bounds hθ hθ1 S x₀ r x).2)
    L hL _ (carrierPosteriorConditional_measurable π F hθ hθ1 S x₀ r L hL)
    (carrierSampleMarginal_pos π F hθ hθ1 S x₀ r)
    (carrierPosteriorConditional_weight π F hθ hθ1 S x₀ r L)

end CausalLowerbound.PartC

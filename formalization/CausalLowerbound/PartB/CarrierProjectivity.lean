import CausalLowerbound.DiscreteIntegration
import CausalLowerbound.PartB.PhysicalCarrierIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-! Exact projectivity of the actual countable density carrier. The atom
dictionary is fixed by Q, also when the number of retained sites is smaller. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] Real.fact_zero_lt_one
local instance projectionCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance projectionCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance projectionCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {d K G : Type*} [Fintype d] [DecidableEq d] [Fintype K] [Fintype G]

def densityTensor (Q : ℕ) (θ : ℝ) (H : ℕ) (u : K → Torus d) : ℝ :=
  ∏ i, labeledDensity Q θ H (u i)

theorem densityTensor_continuous (Q : ℕ) (θ : ℝ) (H : ℕ) :
    Continuous (densityTensor (K := K) (d := d) Q θ H) := by
  exact continuous_finset_prod _ (fun i _ =>
    (labeledDensity_continuous Q θ H).comp (continuous_apply i))

theorem densityTensor_bounds (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (H : ℕ) (u : K → Torus d) :
    (1 - θ) ^ Fintype.card K ≤ densityTensor Q θ H u ∧
      densityTensor Q θ H u ≤ (1 + θ) ^ Fintype.card K := by
  have h0 : 0 ≤ 1 - θ := by linarith
  constructor
  · simpa [densityTensor] using Finset.prod_le_prod (s := Finset.univ)
      (f := fun _ : K => 1 - θ) (fun _ _ => h0)
      (fun i _ => (labeledDensity_bounds Q θ hθ H (u i)).1)
  · simpa [densityTensor] using Finset.prod_le_prod (s := Finset.univ)
      (f := fun i : K => labeledDensity Q θ H (u i))
      (fun i _ => h0.trans (labeledDensity_bounds Q θ hθ H (u i)).1)
      (fun i _ => (labeledDensity_bounds Q θ hθ H (u i)).2)

theorem densityTensor_abs_le (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (H : ℕ) (u : K → Torus d) :
    |densityTensor Q θ H u| ≤ (1 + θ) ^ Fintype.card K := by
  have hb := densityTensor_bounds Q θ hθ hθ1 H u
  rw [abs_of_nonneg ((pow_nonneg (by linarith : 0 ≤ 1 - θ) _).trans hb.1)]
  exact hb.2

theorem densityTensor_integral (Q : ℕ) (θ : ℝ) (H : ℕ) :
    (∫ u : K → Torus d, densityTensor Q θ H u) = 1 := by
  simp only [densityTensor]
  rw [integral_fintype_prod_eq_prod]
  simp only [labeledDensity_integral, Finset.prod_const_one]

theorem densityTensor_sum (Q : ℕ) (θ : ℝ) (H : ℕ)
    (u : K → Torus d) (z : G → Torus d) :
    densityTensor Q θ H (Sum.elim u z) = densityTensor Q θ H u * densityTensor Q θ H z := by
  simp [densityTensor, Fintype.prod_sum_type]

def densityMoment (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ) (u : K → Torus d) : ℝ :=
  H.expect (fun label => densityTensor Q θ label u)

theorem densityMoment_bounds (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (u : K → Torus d) :
    (1 - θ) ^ Fintype.card K ≤ densityMoment H Q θ u ∧
      densityMoment H Q θ u ≤ (1 + θ) ^ Fintype.card K :=
  H.expect_bounds _ _ _ (pow_nonneg (by linarith) _) (fun label =>
    densityTensor_bounds Q θ hθ hθ1 label u)

theorem densityMoment_pos (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (u : K → Torus d) : 0 < densityMoment H Q θ u :=
  (pow_pos (sub_pos.mpr hθ1) _).trans_le (densityMoment_bounds H Q θ hθ hθ1 u).1

theorem densityMoment_continuous (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) : Continuous (densityMoment (K := K) (d := d) H Q θ) :=
  H.expect_continuous _ ((1 + θ) ^ Fintype.card K) (densityTensor_continuous Q θ)
    (densityTensor_abs_le Q θ hθ hθ1)

theorem densityMoment_integral (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    (∫ u : K → Torus d, densityMoment H Q θ u) = 1 := by
  simp only [densityMoment]
  rw [H.integral_expect volume _ ((1 + θ) ^ Fintype.card K)
    (fun label => (densityTensor_continuous Q θ label).aestronglyMeasurable)
    (densityTensor_abs_le Q θ hθ hθ1)]
  simp only [densityTensor_integral, DiscreteLaw.expect, mul_one, H.tsum_weight]

/-- D_q is the genuine marginal of the same Q-slot carrier. -/
theorem densityMoment_projective (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (u : K → Torus d) :
    (∫ z : G → Torus d, densityMoment H Q θ (Sum.elim u z)) = densityMoment H Q θ u := by
  have hc (label : ℕ) : Continuous (fun z : G → Torus d => densityTensor Q θ label (Sum.elim u z)) := by
    simp_rw [densityTensor_sum]
    exact continuous_const.mul (densityTensor_continuous Q θ label)
  simp only [densityMoment]
  rw [H.integral_expect volume _ ((1 + θ) ^ Fintype.card (K ⊕ G))
    (fun label => (hc label).aestronglyMeasurable)
    (fun label z => densityTensor_abs_le Q θ hθ hθ1 label (Sum.elim u z))]
  simp only [densityTensor_sum, integral_const_mul, densityTensor_integral, mul_one, densityMoment]

end CausalLowerbound.PartB.ShellGeometry


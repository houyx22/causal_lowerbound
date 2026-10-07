import CausalLowerbound.PartB.CarrierProjectivity

/-! Projectivity also holds for every bounded label-weighted moment.
The coefficient moment itself is marginalized; no false projectivity of
the tapered increment tensor is asserted. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] Real.fact_zero_lt_one
local instance weightedProjectionCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance weightedProjectionCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance weightedProjectionCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {d K G Γ : Type*} [Fintype d] [DecidableEq d] [Fintype K] [Fintype G] [Fintype Γ]

def weightedDensityMoment (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ) (g : ℕ → ℝ) (u : K → Torus d) : ℝ :=
  H.expect (fun label => densityTensor Q θ label u * g label)

theorem weightedDensityMoment_projective (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (g : ℕ → ℝ) (B : ℝ) (hb : ∀ label, |g label| ≤ B)
    (u : K → Torus d) :
    (∫ z : G → Torus d, weightedDensityMoment H Q θ g (Sum.elim u z)) =
      weightedDensityMoment H Q θ g u := by
  have hc (label : ℕ) : Continuous (fun z : G → Torus d => densityTensor Q θ label (Sum.elim u z) * g label) := by
    simp_rw [densityTensor_sum]
    exact (continuous_const.mul (densityTensor_continuous Q θ label)).mul continuous_const
  have hbound (label : ℕ) (z : G → Torus d) :
      |densityTensor Q θ label (Sum.elim u z) * g label| ≤ (1 + θ) ^ Fintype.card (K ⊕ G) * B := by
    rw [abs_mul]
    exact mul_le_mul (densityTensor_abs_le Q θ hθ hθ1 label _) (hb label)
      (abs_nonneg _) (pow_nonneg (by linarith) _)
  simp only [weightedDensityMoment]
  rw [H.integral_expect volume _ _ (fun label => (hc label).aestronglyMeasurable) hbound]
  simp only [densityTensor_sum, integral_mul_const, integral_const_mul, densityTensor_integral, mul_one]

theorem coefficient_moment_projective (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (P Qk : ℕ → FiniteLaw Γ) (f : Γ → ℝ) (u : K → Torus d) :
    (∫ z : G → Torus d,
      H.expect (fun label => densityTensor Q θ label (Sum.elim u z) *
        ((Qk label).expect f - (P label).expect f))) =
      H.expect (fun label => densityTensor Q θ label u * ((Qk label).expect f - (P label).expect f)) := by
  have hb (x : Γ) : |f x| ≤ ∑ y, |f y| :=
    Finset.single_le_sum (fun y _ => abs_nonneg (f y)) (Finset.mem_univ x)
  apply weightedDensityMoment_projective H Q θ hθ hθ1 _ (2 * ∑ y, |f y|)
  intro label
  exact (abs_sub _ _).trans ((add_le_add
    ((Qk label).abs_expect_le_bound f _ hb) ((P label).abs_expect_le_bound f _ hb)).trans_eq (by ring))

end CausalLowerbound.PartB.ShellGeometry


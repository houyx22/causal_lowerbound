import CausalLowerbound.PartB.CarrierPolynomialMoments
import CausalLowerbound.PartB.WeightedCarrierProjectivity
import CausalLowerbound.PartB.GhostLeakage

/-! Reindexing and exact marginalization of the actual coefficient posterior. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] Real.fact_zero_lt_one
local instance marginalCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance marginalCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance marginalCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {d K G J Γ : Type*} [Fintype d] [DecidableEq d]
  [Fintype K] [Fintype G] [Fintype J] [Fintype Γ]

theorem densityTensor_equiv (Q : ℕ) (θ : ℝ) (label : ℕ) (e : K ≃ J) (u : J → Torus d) :
    densityTensor Q θ label (u ∘ e) = densityTensor Q θ label u := by
  exact e.prod_comp (fun i => labeledDensity Q θ label (u i))

theorem densityMoment_equiv (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (e : K ≃ J) (u : J → Torus d) :
    densityMoment H Q θ (u ∘ e) = densityMoment H Q θ u := by
  simp only [densityMoment, densityTensor_equiv]

theorem coefficientPosterior_difference_equiv (H : DiscreteLaw ℕ) (P Qk : ℕ → FiniteLaw Γ)
    (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (e : K ≃ J)
    (u : J → Torus d) (f : Γ → ℝ) :
    (coefficientPosterior H Qk Q θ hθ hθ1 (u ∘ e)).expect f -
      (coefficientPosterior H P Q θ hθ hθ1 (u ∘ e)).expect f =
    (coefficientPosterior H Qk Q θ hθ hθ1 u).expect f -
      (coefficientPosterior H P Q θ hθ hθ1 u).expect f := by
  simp only [coefficientPosterior_moment_difference, densityMoment_equiv, densityTensor_equiv]

theorem coefficientPosterior_weighted_difference (H : DiscreteLaw ℕ) (P Qk : ℕ → FiniteLaw Γ)
    (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (u : K → Torus d) (f : Γ → ℝ) :
    H.expect (fun label => densityTensor Q θ label u *
      ((Qk label).expect f - (P label).expect f)) = densityMoment H Q θ u *
      ((coefficientPosterior H Qk Q θ hθ hθ1 u).expect f -
        (coefficientPosterior H P Q θ hθ hθ1 u).expect f) := by
  rw [coefficientPosterior_moment_difference, ← mul_assoc,
    mul_inv_cancel₀ (densityMoment_pos H Q θ hθ hθ1 u).ne', one_mul]

/-- Project the weighted numerator first, and then divide by D_q. No
projectivity of the unweighted tapered moment is assumed. -/
theorem coefficientPosterior_ghost_interpolation (H : DiscreteLaw ℕ) (P Qk : ℕ → FiniteLaw Γ)
    (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (χ : (K → Torus d) × (G → Torus d) → ℝ) (u : K → Torus d)
    (f : Γ → ℝ) (c : ℝ)
    (hfull : ∀ z : G → Torus d,
      (coefficientPosterior H Qk Q θ hθ hθ1 (Sum.elim u z)).expect f -
        (coefficientPosterior H P Q θ hθ hθ1 (Sum.elim u z)).expect f = χ (u, z) * c) :
    (coefficientPosterior H Qk Q θ hθ hθ1 u).expect f -
      (coefficientPosterior H P Q θ hθ hθ1 u).expect f = ghostActivation H Q θ χ u * c := by
  have hw (z : G → Torus d) :
      H.expect (fun label => densityTensor Q θ label (Sum.elim u z) *
        ((Qk label).expect f - (P label).expect f)) =
        (completedDensity H Q θ (u, z) * χ (u, z)) * c := by
    rw [coefficientPosterior_weighted_difference, hfull]
    exact (mul_assoc _ _ _).symm
  have hp := coefficient_moment_projective (G := G) H Q θ hθ hθ1 P Qk f u
  simp_rw [hw] at hp
  rw [integral_mul_const] at hp
  rw [coefficientPosterior_moment_difference, ← hp]
  unfold ghostActivation
  ring

end CausalLowerbound.PartB.ShellGeometry

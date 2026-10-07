import CausalLowerbound.PartB.PhysicalDesign

/-! The physical carrier has unit average on its cube, using Haar-to-cube
transport and the Lebesgue change-of-variables theorem. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory UnitAddTorus
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem labeledDensity_integral (Q : ℕ) (θ : ℝ) (H : ℕ) :
    (∫ u : Torus d, labeledDensity Q θ H u) = 1 := by
  cases H with
  | zero => simp [labeledDensity]
  | succ n =>
    have hi : Integrable (toContinuous (PositiveWiener.naturalDensity (d := d) (ι := Fin Q) θ n)) volume :=
      (toContinuous (PositiveWiener.naturalDensity (d := d) (ι := Fin Q) θ n)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    have he := integral_re hi
    rw [PositiveWiener.naturalDensity_integral] at he
    exact he

theorem labeledDensity_cube_integral (Q : ℕ) (θ : ℝ) (H : ℕ) :
    (∫ u in Set.Icc (0 : d → ℝ) 1, labeledDensity Q θ H (torusProjection u)) = 1 := by
  have hcell : unitCell (α := d) =ᵐ[volume] Set.Icc (0 : d → ℝ) 1 := by
    simpa only [unitCell, volume_pi] using
      (Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : d => (volume : Measure ℝ))
        (f := (0 : d → ℝ)) (g := 1))
  rw [← setIntegral_congr_set hcell]
  have he := integral_map (μ := volume.restrict (unitCell (α := d)))
    (torusProjection_measurePreserving (α := d)).measurable.aemeasurable
    (labeledDensity_continuous (d := d) Q θ H).aestronglyMeasurable
  rw [(torusProjection_measurePreserving (α := d)).map_eq] at he
  exact he.symm.trans (labeledDensity_integral Q θ H)

theorem carrierCoordinate_mem_unit_iff (u : d → ℝ) :
    carrierCoordinate u ∈ Set.Icc (0 : d → ℝ) 1 ↔ u ∈ Set.Icc (fun _ => -2) (fun _ => 2) := by
  constructor
  · intro h
    constructor <;> intro i
    · have hi : 0 ≤ u i / 4 + 1 / 2 := h.1 i
      change (-2 : ℝ) ≤ u i
      linarith
    · have hi : u i / 4 + 1 / 2 ≤ 1 := h.2 i
      change u i ≤ (2 : ℝ)
      linarith
  · intro h
    constructor <;> intro i
    · have hi : (-2 : ℝ) ≤ u i := h.1 i
      change 0 ≤ u i / 4 + 1 / 2; linarith
    · have hi : u i ≤ (2 : ℝ) := h.2 i
      change u i / 4 + 1 / 2 ≤ 1; linarith

theorem physicalFactor_integral_zero (Q : ℕ) (θ : ℝ) (H : ℕ)
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ) :
    (∫ x in carrierBox x₀ r k, (physicalFactor Q θ H x₀ r k x - 1)) = 0 := by
  let C : Set (d → ℝ) := Set.Icc 0 1
  let f : (d → ℝ) → ℝ := C.indicator (fun u => labeledDensity Q θ H (torusProjection u) - 1)
  let corner : d → ℝ := fun i => x₀ i + r * k i - 2 * r
  have hc : Continuous (fun u : d → ℝ => labeledDensity Q θ H (torusProjection u)) :=
    (labeledDensity_continuous Q θ H).comp torusProjection_quotient.continuous
  have hfi : (∫ u, f u) = 0 := by
    rw [integral_indicator measurableSet_Icc]
    rw [integral_sub (hc.continuousOn.integrableOn_compact isCompact_Icc)
      ((integrable_const (1 : ℝ) : Integrable (fun _ : d → ℝ => (1 : ℝ)) (cubeMeasure d)))]
    rw [labeledDensity_cube_integral]
    simp [C, measureReal_def, Real.volume_Icc_pi]
  have hcoord (x : d → ℝ) : carrierCoordinate (localCoordinate x₀ r k x) = (4 * r)⁻¹ • (x - corner) := by
    funext i
    dsimp [carrierCoordinate, localCoordinate, corner]
    field_simp
    ring
  have he (x : d → ℝ) : physicalFactor Q θ H x₀ r k x - 1 = f ((4 * r)⁻¹ • (x - corner)) := by
    rw [← hcoord]
    have hm : carrierCoordinate (localCoordinate x₀ r k x) ∈ C ↔ x ∈ carrierBox x₀ r k :=
      carrierCoordinate_mem_unit_iff _
    by_cases hx : x ∈ carrierBox x₀ r k
    · simp [physicalFactor, hx, f, hm.mpr hx]
    · simp [physicalFactor, hx, f, (not_congr hm).mpr hx]
  have hind : (carrierBox x₀ r k).indicator (fun x => physicalFactor Q θ H x₀ r k x - 1) =
      fun x => f ((4 * r)⁻¹ • (x - corner)) := by
    funext x
    by_cases hx : x ∈ carrierBox x₀ r k
    · simpa only [Set.indicator_of_mem hx] using he x
    · rw [Set.indicator_of_not_mem hx, ← he]
      simp [physicalFactor, hx]
  rw [← integral_indicator (carrierBox_measurable x₀ r k), hind]
  rw [integral_sub_right_eq_self (fun y => f ((4 * r)⁻¹ • y)) corner]
  rw [Measure.integral_comp_inv_smul volume f (4 * r), hfi, smul_zero]
end CausalLowerbound.PartB.ShellGeometry

import CausalLowerbound.PartC.PhysicalPropensityTarget
import CausalLowerbound.PartC.AssignmentInterior
import CausalLowerbound.PartC.CarriedField
import CausalLowerbound.PartC.PhysicalRepresentativeEvaluation

/-! Calibration of the local bridge with the actual carried field and
assignment multiplier. The normalization N cancels exactly, and the
resulting effect is the assignment weight times the physical target. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem roughChartPoint_local_coordinate (x₀ : d → ℝ) (r : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (u : d → ℝ) :
    r⁻¹ • (roughChartPoint x₀ r k u - packetCenter x₀ r k) = (fun i => 4 * u i - 2) := by
  funext i
  simp only [roughChartPoint, packetCenter, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  <;> ring

theorem carriedProfile_at_roughChart {Q : ℕ} (U : CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (r : ℝ) (hr : r ≠ 0) (k : d → ℤ) (u : d → ℝ) :
    rescaled (carriedProfile U) (packetCenter x₀ r k) r (roughChartPoint x₀ r k u) =
      linearPartition (fun i => 4 * u i - 2) * coefficientEvaluation U u := by
  rw [rescaled, roughChartPoint_local_coordinate x₀ r hr k u, carriedProfile]
  have he : carrierCoordinate (fun i => 4 * u i - 2) = u := by
    funext i
    simp only [carrierCoordinate]
    ring
  rw [he]

theorem assignmentWeight_at_roughChart (w : ℝ) (x₀ : d → ℝ) (r : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (u : d → ℝ) :
    assignmentWeight w x₀ r k (roughChartPoint x₀ r k u) = assignmentPartition w (fun i => 4 * u i - 2) := by
  rw [assignmentWeight, rescaled, roughChartPoint_local_coordinate x₀ r hr k u]

theorem normalizedRoughChart_eq_scale (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) :
    normalizedRoughChart x₀ ℓ r h k c w N ζ u =
      (assignmentMultiplier c w (fun i => 4 * u i - 2) / N) *
        physicalRoughField x₀ ℓ h ζ (roughChartPoint x₀ r k u) := by
  unfold normalizedRoughChart
  ring

theorem physicalPropensitySlotCorrection_eq_variance {V : Type*}
    (x₀ : d → ℝ) (r h : ℝ) (k : d → ℤ) (c w N ja : ℝ) (u : V × d → ℝ) (i : V) :
    physicalPropensitySlotCorrection x₀ r h k c w N ja u i =
      (assignmentMultiplier c w (fun j => 4 * u (i, j) - 2) / N) ^ 2 * ja ^ 2 *
        (coarseBump x₀ h (roughChartPoint x₀ r k (fun j => u (i, j))) ^ 2) ^ 2 := by
  unfold physicalPropensitySlotCorrection roughChartPoint
  ring

theorem physical_propensity_shift_amplitude (x₀ : d → ℝ) (r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N ja b t : ℝ) (hN : N ≠ 0)
    (hm : ∀ y : d → ℝ, assignmentMultiplier c w y * linearPartition y = assignmentPartition w y)
    (u : d → ℝ) :
    ja * ((b * linearPartition (fun i => 4 * u i - 2)) * (t * N)) *
      (assignmentMultiplier c w (fun i => 4 * u i - 2) / N) *
        coarseBump x₀ h (roughChartPoint x₀ r k u) ^ 2 =
      assignmentWeight w x₀ r k (roughChartPoint x₀ r k u) *
        targetField x₀ h (ja * b * t) (roughChartPoint x₀ r k u) := by
  rw [assignmentWeight_at_roughChart w x₀ r hr k u, targetField]
  calc
    _ = (assignmentMultiplier c w (fun i => 4 * u i - 2) * linearPartition (fun i => 4 * u i - 2)) *
        ((ja * b * t) * coarseBump x₀ h (roughChartPoint x₀ r k u) ^ 2) := by
      field_simp
      <;> ring
    _ = _ := by rw [hm]

end CausalLowerbound.PartC

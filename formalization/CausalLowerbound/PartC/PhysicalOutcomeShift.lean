import CausalLowerbound.PartC.NormalizedOutcomeBridge
import CausalLowerbound.PartC.PhysicalPropensityShift

/-! At an assigned interior site, the normalized virtual coefficient
shift is exactly the physical smooth jitter. Consequently the actual
fourth-moment correction supplies the normalized cubic bridge. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry RoughOutcome
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem physical_outcome_shift_scale (x₀ : d → ℝ) (r : ℝ) (hr : r ≠ 0) (k : d → ℤ)
    (c w N a t : ℝ) (hN : N ≠ 0)
    (hm : ∀ y : d → ℝ, assignmentMultiplier c w y * linearPartition y = assignmentPartition w y)
    (u : d → ℝ) :
    (a * linearPartition (fun j => 4 * u j - 2) * (t * N)) *
      (assignmentMultiplier c w (fun j => 4 * u j - 2) / N) =
        a * t * assignmentWeight w x₀ r k (roughChartPoint x₀ r k u) := by
  rw [assignmentWeight_at_roughChart w x₀ r hr k u, ← hm]
  field_simp [hN] <;> ring

theorem physical_outcome_assigned_bridge (x₀ : d → ℝ) (ℓ r h : ℝ)
    (hℓ : 0 < ℓ) (hr : r ≠ 0) (hh : 0 < h) (k : d → ℤ)
    (c w N a t jb R T smooth : ℝ) (hN : N ≠ 0)
    (hm : ∀ y : d → ℝ, assignmentMultiplier c w y * linearPartition y = assignmentPartition w y)
    (u : d → ℝ) (howner : assignmentWeight w x₀ r k (roughChartPoint x₀ r k u) = 1)
    (f : Fin 4) :
    let x := roughChartPoint x₀ r k u
    let X := fun ξ => physicalRoughField x₀ ℓ h ξ x
    let scale := assignmentMultiplier c w (fun j => 4 * u j - 2) / N
    let shift := a * linearPartition (fun j => 4 * u j - 2) * (t * N)
    let v := coarseBump x₀ h x ^ 2
    let η := physicalRoughCorrection x₀ ℓ h (a * t) x
    independentSigns.expect (fun ξ =>
      normalizedSubstitution 1 f scale v (X ξ) * incrementOne R T shift jb η smooth (X ξ) +
      normalizedSubstitution 2 f scale v (X ξ) * incrementTwo R T shift jb smooth (X ξ) +
      normalizedSubstitution 3 f scale v (X ξ) * incrementThree R T shift jb (X ξ)) =
    independentSigns.expect (fun ξ => normalizedRoughChart x₀ ℓ r h k c w N ξ u ^ f.val *
      realField R T smooth (targetField x₀ h (a * t * jb) x)) := by
  have hs := physical_outcome_shift_scale x₀ r hr k c w N a t hN hm u
  rw [howner, mul_one] at hs
  have hb := normalized_physical_bridge x₀ ℓ h R T
    (a * linearPartition (fun j => 4 * u j - 2) * (t * N)) jb smooth
    (assignmentMultiplier c w (fun j => 4 * u j - 2) / N) hℓ hh (roughChartPoint x₀ r k u) f
  dsimp only at hb ⊢
  rw [hs] at hb
  simpa only [normalizedRoughChart_eq_scaled, targetField] using hb

end CausalLowerbound.PartC

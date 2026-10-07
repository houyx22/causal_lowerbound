import CausalLowerbound.PartC.PhysicalRepresentativeEvaluation
import CausalLowerbound.PartC.PhysicalRoughMoments
import CausalLowerbound.PartC.OutcomeSubstitution

/-! The first four moments of the actual normalized carrier-chart field.
Its variance is independent of the fine signs and fine scale, including
at points where the assignment multiplier vanishes. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
variable {d : Type*} [Fintype d] [DecidableEq d]

def normalizedRoughVariance (x₀ : d → ℝ) (r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (u : d → ℝ) : ℝ :=
  (assignmentMultiplier c w (fun j => 4 * u j - 2) / N) ^ 2 *
    coarseBump x₀ h (roughChartPoint x₀ r k u) ^ 2

theorem normalizedRoughChart_eq_scaled (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) :
    normalizedRoughChart x₀ ℓ r h k c w N ζ u =
      (assignmentMultiplier c w (fun j => 4 * u j - 2) / N) *
        physicalRoughField x₀ ℓ h ζ (roughChartPoint x₀ r k u) := by
  unfold normalizedRoughChart
  ring

theorem normalizedRoughChart_moments (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h) (u : d → ℝ) :
    independentSigns.expect (fun ζ => normalizedRoughChart x₀ ℓ r h k c w N ζ u) = 0 ∧
    independentSigns.expect (fun ζ => normalizedRoughChart x₀ ℓ r h k c w N ζ u ^ 2) =
      normalizedRoughVariance x₀ r h k c w N u ∧
    independentSigns.expect (fun ζ => normalizedRoughChart x₀ ℓ r h k c w N ζ u ^ 3) = 0 ∧
    independentSigns.expect (fun ζ => normalizedRoughChart x₀ ℓ r h k c w N ζ u ^ 4) =
      normalizedRoughVariance x₀ r h k c w N u ^ 2 *
        (3 - 2 * quarticField (activeBlocks ℓ h) x₀ ℓ (roughChartPoint x₀ r k u)) := by
  obtain ⟨hm, hv, ht, hf⟩ := physicalRoughField_moments x₀ ℓ h hℓ hh (roughChartPoint x₀ r k u)
  simp only [normalizedRoughChart_eq_scaled, mul_pow, FiniteLaw.expect_mul, hm, hv, ht, hf,
    mul_zero, normalizedRoughVariance]
  constructor
  · trivial
  constructor
  · trivial
  constructor
  · trivial
  ring

theorem outcomeMoment_eq_normalizedRoughChart (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h) (u : d → ℝ) (f : Fin 4) :
    Representative.outcomeMoment (normalizedRoughVariance x₀ r h k c w N u) f =
      independentSigns.expect (fun ζ => normalizedRoughChart x₀ ℓ r h k c w N ζ u ^ f.val) := by
  have hm := normalizedRoughChart_moments x₀ ℓ r h k c w N hℓ hh u
  exact outcomeMoment_eq_expect independentSigns _ _ hm.1 hm.2.1 hm.2.2.1 f

end CausalLowerbound.PartC

import CausalLowerbound.PartC.CarrierDesign
import CausalLowerbound.PartC.PairedPhysicalDensity

/-! The global-design interface instantiated with the actual paired
physical densities, for both the degree-one and degree-three carriers. -/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι] {D : ℕ}

def physicalCarrierProfile (x₀ : d → ℝ) (ℓ r h : ℝ) (c w N N₀ θ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ y : d → ℝ, 0 ≤ assignmentMultiplier c w y ∧ assignmentMultiplier c w y ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hθ : 0 ≤ θ)
    (labels : (d → ℤ) → ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) : CarrierProfile d θ where
  density k := carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ (labels k) ζ
  measurable k := (carrierPhysicalDensity_continuous x₀ ℓ r h k c w N θ hc (labels k) ζ).measurable
  bounds k u := carrierPhysicalDensity_range x₀ ℓ r h k c w N N₀ θ
    hℓ hr hc hN₀ hN hm hrough hθ (labels k) ζ u

theorem roughChartPoint_localCoordinate (x₀ : d → ℝ) (r : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (u : d → ℝ) :
    localCoordinate x₀ r k (roughChartPoint x₀ r k u) = fun i => 4 * u i - 2 := by
  funext i
  dsimp only [localCoordinate, roughChartPoint]
  field_simp [hr]
  <;> ring

theorem CarrierProfile.factor_chart {θ : ℝ} (F : CarrierProfile d θ)
    (x₀ : d → ℝ) (r : ℝ) (hr : r ≠ 0) (k : d → ℤ) (u : d → ℝ)
    (hu : u ∈ Set.Icc (0 : d → ℝ) 1) :
    F.factor x₀ r k (roughChartPoint x₀ r k u) = F.density k u := by
  have hl := roughChartPoint_localCoordinate x₀ r hr k u
  have hx : roughChartPoint x₀ r k u ∈ carrierBox x₀ r k := by
    change (fun _ => (-2 : ℝ)) ≤ localCoordinate x₀ r k (roughChartPoint x₀ r k u) ∧
      localCoordinate x₀ r k (roughChartPoint x₀ r k u) ≤ (fun _ => (2 : ℝ))
    rw [hl]
    constructor <;> intro i
    · have h₀ : 0 ≤ u i := hu.1 i
      change -2 ≤ 4 * u i - 2
      linarith
    · have h₁ : u i ≤ 1 := hu.2 i
      change 4 * u i - 2 ≤ 2
      linarith
  rw [factor, if_pos hx, hl]
  congr 1
  funext i
  dsimp only [carrierCoordinate]
  ring

end CausalLowerbound.PartC

import CausalLowerbound.PartC.PhysicalLocalSigns
import CausalLowerbound.PartC.PhysicalCarrierDesign

/-! The finite set of rough symbols read anywhere in a carrier box.
The centering integrals have exactly zero coefficients in every other
symbol, not merely a small one-symbol norm. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def carrierLocalSigns (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) :
    Finset (activeBlocks (d := d) ℓ h) :=
  Finset.univ.filter (fun j => ∃ x ∈ carrierBox x₀ r k, j ∈ physicalLocalSigns x₀ ℓ h x)

theorem mem_carrierLocalSigns (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (j : activeBlocks (d := d) ℓ h) :
    j ∈ carrierLocalSigns x₀ ℓ r h k ↔
      ∃ x ∈ carrierBox x₀ r k, j ∈ physicalLocalSigns x₀ ℓ h x := by
  simp only [carrierLocalSigns, Finset.mem_filter, Finset.mem_univ, true_and]

theorem physicalLocalSigns_subset_carrier (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (x : d → ℝ) (hx : x ∈ carrierBox x₀ r k) :
    physicalLocalSigns x₀ ℓ h x ⊆ carrierLocalSigns x₀ ℓ r h k := by
  intro j hj
  exact (mem_carrierLocalSigns x₀ ℓ r h k j).mpr ⟨x, hx, hj⟩

theorem packet_zero_outside_carrierLocalSigns (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (j : activeBlocks (d := d) ℓ h) (hj : j ∉ carrierLocalSigns x₀ ℓ r h k)
    (x : d → ℝ) (hx : x ∈ carrierBox x₀ r k) :
    packet (coarseBump x₀ h) x₀ ℓ j.val x = 0 := by
  by_contra hp
  apply hj
  apply physicalLocalSigns_subset_carrier x₀ ℓ r h k x hx
  simpa only [physicalLocalSigns, Finset.mem_filter, Finset.mem_univ, true_and] using hp

theorem roughChartPoint_mem_carrierBox (x₀ : d → ℝ) (r : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (u : d → ℝ) (hu : u ∈ Set.Icc (0 : d → ℝ) 1) :
    roughChartPoint x₀ r k u ∈ carrierBox x₀ r k := by
  change (fun _ => (-2 : ℝ)) ≤ localCoordinate x₀ r k (roughChartPoint x₀ r k u) ∧
    localCoordinate x₀ r k (roughChartPoint x₀ r k u) ≤ (fun _ => (2 : ℝ))
  rw [roughChartPoint_localCoordinate x₀ r hr k u]
  constructor <;> intro i
  · have hi : 0 ≤ u i := hu.1 i
    change -2 ≤ 4 * u i - 2
    linarith
  · have hi : u i ≤ 1 := hu.2 i
    change 4 * u i - 2 ≤ 2
    linarith

theorem normalizedRoughChart_local_congr (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N : ℝ) (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (hζ : ∀ j ∈ carrierLocalSigns x₀ ℓ r h k, ζ j = ζ' j)
    (u : d → ℝ) (hu : u ∈ Set.Icc (0 : d → ℝ) 1) :
    normalizedRoughChart x₀ ℓ r h k c w N ζ u =
      normalizedRoughChart x₀ ℓ r h k c w N ζ' u := by
  have hx := roughChartPoint_mem_carrierBox x₀ r hr k u hu
  have he := physicalRoughField_local_congr x₀ ℓ h (roughChartPoint x₀ r k u) ζ ζ'
    (fun j hj => hζ j (physicalLocalSigns_subset_carrier x₀ ℓ r h k _ hx hj))
  unfold normalizedRoughChart
  rw [he]

theorem roughCentering_symbol_zero (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (n : ℕ) (w : (d → ℝ) → ℝ) (hw : Continuous w)
    (j : activeBlocks (d := d) ℓ h) (hj : j ∉ carrierLocalSigns x₀ ℓ r h k) :
    Walsh.symbolPart j (roughCentering x₀ ℓ r h k n w) = 0 := by
  have hz (u : d → ℝ) (hu : u ∈ Set.Icc (0 : d → ℝ) 1) :
      Walsh.symbolPart j (Walsh.power (physicalRoughWalsh x₀ ℓ h (roughChartPoint x₀ r k u)) n) = 0 := by
    have hp := packet_zero_outside_carrierLocalSigns x₀ ℓ r h k j hj _
      (roughChartPoint_mem_carrierBox x₀ r hr k u hu)
    have hb := physicalRoughWalsh_power_symbol x₀ ℓ h (roughChartPoint x₀ r k u) j n
      ‖physicalRoughWalsh x₀ ℓ h (roughChartPoint x₀ r k u)‖ le_rfl
    rw [hp, abs_zero, mul_zero] at hb
    exact norm_le_zero_iff.mp hb
  rw [roughCentering, ← (Walsh.symbolPart j).integral_comp_comm
    (roughCentering_integrable x₀ ℓ r h k n w hw)]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [map_smul, hz u hu, smul_zero]
  rfl

theorem normalizedTrigCenter_symbol_zero (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N : ℝ) (hc : 0 < c) (n : ℕ) (q : d → ℤ) (b : Bool)
    (j : activeBlocks (d := d) ℓ h) (hj : j ∉ carrierLocalSigns x₀ ℓ r h k) :
    Walsh.symbolPart j (normalizedTrigCenter x₀ ℓ r h k c w N n q b) = 0 :=
  roughCentering_symbol_zero x₀ ℓ r h hr k n _ (normalizedTrigWeight_continuous c w N hc n q b) j hj

end CausalLowerbound.PartC

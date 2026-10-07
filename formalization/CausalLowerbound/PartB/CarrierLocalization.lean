import CausalLowerbound.PartB.PhysicalCarrierIntegral

/-! The actual finite carrier family fits inside the observation cube once
the coarse scale is small relative to the fixed interior point. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace CausalLowerbound.PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem active_carrier_distance (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hrh : r ≤ h)
    (k : d → ℤ) (hk : k ∈ activeBlocks (d := d) r h) (x : d → ℝ)
    (hx : x ∈ carrierBox x₀ r k) (i : d) : |x i - x₀ i| ≤ 5 * h := by
  have hki := Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hk) i)
  have hk₁ : -(⌈h / r + 1⌉ : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hki.1
  have hk₂ : (k i : ℝ) ≤ (⌈h / r + 1⌉ : ℝ) := by exact_mod_cast hki.2
  have habs : |(k i : ℝ)| ≤ h / r + 2 := by
    have he := Int.ceil_lt_add_one (h / r + 1)
    have hb := abs_le.mpr ⟨hk₁, hk₂⟩
    linarith
  have hl : (-2 : ℝ) ≤ (x i - x₀ i) / r - k i := hx.1 i
  have hu : (x i - x₀ i) / r - k i ≤ (2 : ℝ) := hx.2 i
  have hp := abs_add ((x i - x₀ i) / r - k i) (k i : ℝ)
  have he : (x i - x₀ i) / r - k i + k i = (x i - x₀ i) / r := by ring
  rw [he] at hp
  have hv : |(x i - x₀ i) / r| ≤ h / r + 4 := by linarith [(abs_le.mpr ⟨hl, hu⟩)]
  rw [abs_div, abs_of_pos hr] at hv
  have hb := (div_le_iff₀ hr).mp hv
  have hh : (h / r + 4) * r = h + 4 * r := by field_simp
  rw [hh] at hb
  linarith

theorem active_carrier_inside_cube (x₀ : d → ℝ) (δ r h : ℝ)
    (hcenter : ∀ i, δ ≤ x₀ i ∧ x₀ i ≤ 1 - δ) (hr : 0 < r) (hrh : r ≤ h) (hh : 5 * h ≤ δ)
    (k : d → ℤ) (hk : k ∈ activeBlocks (d := d) r h) :
    carrierBox x₀ r k ⊆ Set.Icc (0 : d → ℝ) 1 := by
  intro x hx
  constructor <;> intro i
  · have hb := abs_le.mp (active_carrier_distance x₀ r h hr hrh k hk x hx i)
    have hc := hcenter i
    change 0 ≤ x i
    linarith
  · have hb := abs_le.mp (active_carrier_distance x₀ r h hr hrh k hk x hx i)
    have hc := hcenter i
    change x i ≤ 1
    linarith
end CausalLowerbound.PartB.ShellGeometry

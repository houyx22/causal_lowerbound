import CausalLowerbound.PartC.RepresentativeEvaluation
import CausalLowerbound.PartC.RoughWalshCentering
import CausalLowerbound.PartC.AssignmentMultiplier
import CausalLowerbound.PeriodizedTorus

/-! Evaluation on the actual closed carrier chart. Its normalization is
uniform in the fine scale, carrier block, signs, and representative degree. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry Representative

abbrev UnitChart (d : Type*) := ↥(Set.Icc (0 : d → ℝ) 1)

variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι]

def normalizedRoughChart (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) : ℝ :=
  assignmentMultiplier c w (fun j => 4 * u j - 2) *
    physicalRoughField x₀ ℓ h ζ (roughChartPoint x₀ r k u) / N

theorem normalizedRoughChart_continuous (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ)
    (hc : 0 < c) (ζ : activeBlocks (d := d) ℓ h → Bool) :
    Continuous (normalizedRoughChart x₀ ℓ r h k c w N ζ) := by
  have hfield : Continuous (physicalRoughField x₀ ℓ h ζ) := by
    have h := (Walsh.evaluate ζ).continuous.comp (physicalRoughWalsh_continuous x₀ ℓ h)
    simpa only [Function.comp_def, physicalRoughWalsh_evaluate] using h
  have hcoord : Continuous (fun u : d → ℝ => fun j => 4 * u j - 2) := by fun_prop
  simpa only [normalizedRoughChart, div_eq_mul_inv] using
    (((assignmentMultiplier_smooth c w hc).continuous.comp hcoord).mul
      (hfield.comp (roughChartPoint_continuous x₀ r k))).mul
        (continuous_const (y := N⁻¹))

theorem normalizedRoughChart_bound (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N N₀ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) :
    |normalizedRoughChart x₀ ℓ r h k c w N ζ u| ≤ 1 := by
  have hNp : 0 < N := (div_pos hN₀ hc).trans_le hN
  have hf : |physicalRoughField x₀ ℓ h ζ (roughChartPoint x₀ r k u)| ≤ N₀ := by
    rw [← physicalRoughWalsh_evaluate]
    exact (Walsh.evaluate_bound ζ _).trans (hrough _)
  rw [normalizedRoughChart, abs_div, abs_mul, abs_of_pos hNp,
    abs_of_nonneg (hm _).1, div_le_one hNp]
  calc
    _ ≤ (1 / c) * N₀ := mul_le_mul (hm _).2 hf (abs_nonneg _) (by positivity)
    _ = N₀ / c := by ring
    _ ≤ N := hN

/-- The constants are constructed from the actual assignment multiplier and
rough packets. No evaluation or norm bound is an external input. -/
theorem exists_physical_chart_evaluation (D : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, 0 < N₀ ∧
      ∀ (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (w N : ℝ),
        0 < ℓ → ℓ ≤ h → 0 < w → w ≤ 1 / 2 → N₀ / c ≤ N →
        ∃ ev : (activeBlocks (d := d) ℓ h → Bool) →
          Array d ι (activeBlocks (d := d) ℓ h) D →L[ℝ] C(UnitChart (ι × d), ℝ),
          (∀ ζ a u, ev ζ a u = pointValue (Wiener.torusProjection u.val)
            (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u.val (i, j))) ζ a) ∧
          (∀ ζ a, ‖ev ζ a‖ ≤ ‖a‖) ∧
          (∀ ζ u, ev ζ unit u = 1) := by
  obtain ⟨c, hc, _, hm⟩ := exists_assignmentMultiplier (d := d)
  obtain ⟨N₀, hN₀, hrough⟩ := physicalRoughWalsh_bound (d := d)
  refine ⟨c, hc, N₀, hN₀, fun x₀ ℓ r h k w N hℓ hℓh hw hw1 hN => ?_⟩
  let chart : UnitChart (ι × d) → Wiener.Torus (ι × d) :=
    fun u => Wiener.torusProjection u.val
  have hchart : Continuous chart := Wiener.torusProjection_quotient.continuous.comp continuous_subtype_val
  let z (ζ : activeBlocks (d := d) ℓ h → Bool) (i : ι) (u : UnitChart (ι × d)) :=
    normalizedRoughChart x₀ ℓ r h k c w N ζ (fun j => u.val (i, j))
  have hz (ζ : activeBlocks (d := d) ℓ h → Bool) (i : ι) : Continuous (z ζ i) :=
    (normalizedRoughChart_continuous x₀ ℓ r h k c w N hc ζ).comp
      (continuous_pi (fun j => (continuous_apply (i, j)).comp continuous_subtype_val))
  have hb (ζ : activeBlocks (d := d) ℓ h → Bool) (i : ι) (u : UnitChart (ι × d)) :
      |z ζ i u| ≤ 1 := normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN
        (fun v => ((hm w hw hw1).2.2 v).2) (hrough x₀ ℓ h hℓ hℓh) ζ _
  refine ⟨fun ζ => chartEvaluation chart hchart (z ζ) (hz ζ) (hb ζ) ζ, ?_, ?_, ?_⟩
  · intro ζ a u
    rfl
  · intro ζ a
    exact chartEvaluation_bound _ _ _ _ _ _ _
  · intro ζ u
    exact pointValue_unit _ _ _

end CausalLowerbound.PartC

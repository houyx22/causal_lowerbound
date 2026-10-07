import CausalLowerbound.PartC.WeightedPropensityPatterns
import CausalLowerbound.PartC.PhysicalPropensityShift

/-! Uniform bounds after absorbing N into the selected physical slots.
The constants depend only on the fixed multiplier floor and rough-field
bound, not on N, packet counts, block locations, or physical scales. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative Wiener
variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]

theorem normalized_assignment_ratio_bound (c w N N₀ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀)
    (hN : N₀ / c ≤ N) (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧
      assignmentMultiplier c w v ≤ 1 / c) (v : d → ℝ) :
    assignmentMultiplier c w v / N ≤ 1 / N₀ := by
  have hNp : 0 < N := (div_pos hN₀ hc).trans_le hN
  apply (div_le_div_iff₀ hNp hN₀).mpr
  calc
    _ ≤ (1 / c) * N₀ := mul_le_mul_of_nonneg_right (hm v).2 hN₀.le
    _ = N₀ / c := by ring
    _ ≤ 1 * N := by simpa only [one_mul] using hN

theorem normalizedRoughChart_scaled_bound (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) :
    |N * normalizedRoughChart x₀ ℓ r h k c w N ζ u| ≤ N₀ / c := by
  have hNp : 0 < N := (div_pos hN₀ hc).trans_le hN
  have hf : |physicalRoughField x₀ ℓ h ζ (roughChartPoint x₀ r k u)| ≤ N₀ := by
    rw [← physicalRoughWalsh_evaluate]
    exact (Walsh.evaluate_bound ζ _).trans (hrough _)
  have he : N * normalizedRoughChart x₀ ℓ r h k c w N ζ u =
      assignmentMultiplier c w (fun i => 4 * u i - 2) *
        physicalRoughField x₀ ℓ h ζ (roughChartPoint x₀ r k u) := by
    unfold normalizedRoughChart
    field_simp
  rw [he, abs_mul, abs_of_nonneg (hm _).1]
  exact (mul_le_mul (hm _).2 hf (abs_nonneg _) (by positivity)).trans_eq (by ring)

theorem physicalPropensityCorrection_scaled_bound (x₀ : d → ℝ) (r h : ℝ) (k : d → ℤ)
    (c w N N₀ ja : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hja : ja ^ 2 ≤ 1) (u : V × d → ℝ) (i : V) :
    |N * physicalPropensitySlotCorrection x₀ r h k c w N ja u i| ≤ 1 / (c * N₀) := by
  have hNp : 0 < N := (div_pos hN₀ hc).trans_le hN
  let m := assignmentMultiplier c w (fun j => 4 * u (i, j) - 2)
  let G := coarseBump x₀ h (fun j => x₀ j + r * (k j + 4 * u (i, j) - 2))
  have hm0 : 0 ≤ m := (hm _).1
  have hmc : m ≤ 1 / c := (hm _).2
  have hratio : m / N ≤ 1 / N₀ := normalized_assignment_ratio_bound c w N N₀ hc hN₀ hN hm _
  have hG : G ∈ Set.Icc 0 1 := coarseBump_range x₀ h _
  have he : N * physicalPropensitySlotCorrection x₀ r h k c w N ja u i =
      (m / N) * m * ja ^ 2 * G ^ 4 := by
    dsimp [physicalPropensitySlotCorrection, m, G]
    field_simp
    <;> ring
  rw [he, abs_of_nonneg (by positivity)]
  have hb : (m / N) * m ≤ (1 / N₀) * (1 / c) :=
    mul_le_mul hratio hmc hm0 (by positivity)
  have hb' : (m / N) * m * ja ^ 2 ≤ ((1 / N₀) * (1 / c)) * 1 :=
    mul_le_mul hb hja (sq_nonneg _) (by positivity)
  have hb'' := mul_le_mul hb' (pow_le_one₀ hG.1 hG.2 (n := 4)) (pow_nonneg hG.1 4)
    (show 0 ≤ ((1 / N₀) * (1 / c)) * 1 by positivity)
  exact hb''.trans_eq (by ring)

theorem physical_weightedPropensityPattern_bound (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ ja : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hja : ja ^ 2 ≤ 1)
    (W : Array d V (activeBlocks (d := d) ℓ h) 1) (u : V × d → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (S : Finset V) :
    |weightedPropensityPatternWeight N (physicalPropensitySlotCorrection x₀ r h k c w N ja u)
      W u (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (configurationSite u i)) ζ S| ≤
        (1 + N₀ / c + 1 / (c * N₀)) ^ Fintype.card V * ‖W‖ := by
  have hb₁ : 0 ≤ N₀ / c := by positivity
  have hb₂ : 0 ≤ 1 / (c * N₀) := by positivity
  apply weightedPropensityPatternWeight_bound N _ W u _ ζ S _ (by linarith)
  · intro i
    exact normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ _
  · intro i
    exact (normalizedRoughChart_scaled_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ _).trans (by linarith)
  · intro i
    exact (physicalPropensityCorrection_scaled_bound x₀ r h k c w N N₀ ja hc hN₀ hN hm hja u i).trans (by linarith)

end CausalLowerbound.PartC

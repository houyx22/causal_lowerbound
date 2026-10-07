import CausalLowerbound.PartC.WeightedOutcomePatterns
import CausalLowerbound.PartC.PhysicalPatternBounds
import CausalLowerbound.PartC.NormalizedRoughMoments

/-! Uniform real bounds for the actual cubic pattern weights. The
constant depends on the multiplier floor and the rough-field bound,
but is independent of N, fine packet count, and the physical scales. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative Wiener
variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]

theorem normalizedRoughVariance_bound (x₀ : d → ℝ) (r h : ℝ) (k : d → ℤ)
    (c w N N₀ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (u : d → ℝ) : |normalizedRoughVariance x₀ r h k c w N u| ≤ 1 / N₀ ^ 2 := by
  have hNp : 0 < N := (div_pos hN₀ hc).trans_le hN
  have hr := normalized_assignment_ratio_bound c w N N₀ hc hN₀ hN hm (fun j => 4 * u j - 2)
  have hr0 : 0 ≤ assignmentMultiplier c w (fun j => 4 * u j - 2) / N :=
    div_nonneg (hm _).1 hNp.le
  have hG := coarseBump_range x₀ h (roughChartPoint x₀ r k u)
  rw [normalizedRoughVariance, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  calc
    _ ≤ (1 / N₀) ^ 2 * 1 := mul_le_mul (pow_le_pow_left₀ hr0 hr 2)
      (pow_le_one₀ hG.1 hG.2) (sq_nonneg _) (sq_nonneg _)
    _ = _ := by simp only [div_pow, one_pow, mul_one]

theorem physical_weightedOutcomePattern_bound (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (W : Array d V (activeBlocks (d := d) ℓ h) 3) (u : V × d → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : Degree V 3) :
    |weightedOutcomePatternWeight N
      (fun i => normalizedRoughVariance x₀ r h k c w N (configurationSite u i)) W u
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (configurationSite u i)) ζ e| ≤
        ((1 + N₀ / c + 1 / N₀ ^ 2) ^ 4) ^ Fintype.card V * ‖W‖ := by
  have hb₁ : 0 ≤ N₀ / c := by positivity
  have hb₂ : 0 ≤ 1 / N₀ ^ 2 := by positivity
  apply weightedOutcomePatternWeight_bound N _ W u _ ζ e _ (by linarith)
  · intro i
    exact normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ _
  · intro i
    exact (normalizedRoughChart_scaled_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ _).trans (by linarith)
  · intro i
    exact (normalizedRoughVariance_bound x₀ r h k c w N N₀ hc hN₀ hN hm _).trans (by linarith)

end CausalLowerbound.PartC

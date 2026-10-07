import CausalLowerbound.PartC.CrudeOutcomeComparison

/-! A finite uniform Hellinger constant for components of at most Q sites.
The incident-block count is at most Q times the fixed geometric overlap,
so this constant is independent of the total number of active blocks. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC

def outcomeCrudeHellingerCoefficient (Q q k D : ℕ) (c N₀ θ κ : ℝ) : ℝ :=
  (4 : ℝ) ^ q *
    (outcomeCrudeConstant Q q k c N₀ / ((1 - θ) ^ (5 ^ D)) ^ q) ^ 2 / (κ ^ 2) ^ q

theorem outcomeCrudeHellingerCoefficient_nonneg (Q q k D : ℕ) (c N₀ θ κ : ℝ) :
    0 ≤ outcomeCrudeHellingerCoefficient Q q k D c N₀ θ κ := by
  unfold outcomeCrudeHellingerCoefficient
  positivity

def outcomeLocalCrudeConstant (Q D : ℕ) (c N₀ θ κ : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (Q + 1), ∑ k ∈ Finset.range (Q * 5 ^ D + 1),
    outcomeCrudeHellingerCoefficient Q q k D c N₀ θ κ

theorem outcomeLocalCrudeConstant_nonneg (Q D : ℕ) (c N₀ θ κ : ℝ) :
    0 ≤ outcomeLocalCrudeConstant Q D c N₀ θ κ := by
  exact Finset.sum_nonneg (fun q _ => Finset.sum_nonneg
    (fun k _ => outcomeCrudeHellingerCoefficient_nonneg Q q k D c N₀ θ κ))

theorem outcomeCrudeHellingerCoefficient_le_uniform (Q q k D : ℕ) (c N₀ θ κ : ℝ)
    (hq : q ≤ Q) (hk : k ≤ Q * 5 ^ D) :
    outcomeCrudeHellingerCoefficient Q q k D c N₀ θ κ ≤
      outcomeLocalCrudeConstant Q D c N₀ θ κ := by
  apply (Finset.single_le_sum
    (fun k _ => outcomeCrudeHellingerCoefficient_nonneg Q q k D c N₀ θ κ)
    (Finset.mem_range.mpr (by omega : k < Q * 5 ^ D + 1))).trans
  exact Finset.single_le_sum
    (fun q _ => Finset.sum_nonneg (fun k _ => outcomeCrudeHellingerCoefficient_nonneg Q q k D c N₀ θ κ))
    (Finset.mem_range.mpr (by omega : q < Q + 1))

theorem outcomeCrudeHellingerCoefficient_mul_sq (Q q k D : ℕ) (c N₀ θ κ a : ℝ) :
    (4 : ℝ) ^ q *
      (outcomeCrudeConstant Q q k c N₀ * |a| / ((1 - θ) ^ (5 ^ D)) ^ q) ^ 2 / (κ ^ 2) ^ q =
        outcomeCrudeHellingerCoefficient Q q k D c N₀ θ κ * a ^ 2 := by
  simp only [outcomeCrudeHellingerCoefficient, div_pow, mul_pow, sq_abs]
  ring

end CausalLowerbound.PartC

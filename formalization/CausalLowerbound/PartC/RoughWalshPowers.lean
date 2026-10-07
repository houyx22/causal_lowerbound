import CausalLowerbound.PartC.WalshProduct
import CausalLowerbound.PartC.PhysicalRoughWalsh

/-! Continuous Walsh arrays for all powers of the actual rough field. The
single-symbol estimate retains one localized packet, independently of how many
other symbols occur in the field. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators symmDiff

namespace CausalLowerbound.PartC

namespace Walsh

variable {J X : Type*} [Fintype J] [DecidableEq J] [TopologicalSpace X]

theorem continuous_product (a b : X → Coefficients J) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => product (a x) (b x)) := by
  unfold product
  apply continuous_finset_sum
  intro S _
  apply continuous_finset_sum
  intro T _
  exact (lp.singleContinuousLinearMap ℝ (fun _ : Finset J => ℝ) 1 (S ∆ T)).continuous.comp
    (((Wiener.entry S).continuous.comp ha).mul ((Wiener.entry T).continuous.comp hb))

theorem continuous_power (a : X → Coefficients J) (ha : Continuous a) (n : ℕ) :
    Continuous (fun x => power (a x) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact continuous_product a (fun x => power (a x) n) ha ih

end Walsh

open PartB PartB.ShellGeometry

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem physicalRoughWalsh_continuous (x₀ : d → ℝ) (ℓ h : ℝ) :
    Continuous (physicalRoughWalsh x₀ ℓ h) := by
  unfold physicalRoughWalsh
  apply continuous_finset_sum
  intro k _
  apply (lp.singleContinuousLinearMap ℝ
    (fun _ : Finset (activeBlocks (d := d) ℓ h) => ℝ) 1 {k}).continuous.comp
  simpa only [physicalJitterWeights, one_mul] using
    (packet_smooth _ (rescaled_smooth _ quadraticPartition_smooth _ _) x₀ ℓ k.val).continuous

theorem physicalRoughWalsh_power_evaluate (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (n : ℕ) :
    Walsh.evaluate ζ (Walsh.power (physicalRoughWalsh x₀ ℓ h x) n) =
      physicalRoughField x₀ ℓ h ζ x ^ n := by
  rw [Walsh.evaluate_power, physicalRoughWalsh_evaluate]

theorem physicalRoughWalsh_power_symbol (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ)
    (j : activeBlocks (d := d) ℓ h) (n : ℕ) (N₀ : ℝ)
    (hN : ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) :
    ‖Walsh.symbolPart j (Walsh.power (physicalRoughWalsh x₀ ℓ h x) n)‖ ≤
      (n : ℝ) * N₀ ^ (n - 1) * |packet (coarseBump x₀ h) x₀ ℓ j.val x| := by
  apply (Walsh.power_symbol_bound j _ n).trans
  rw [physicalRoughWalsh_symbol_norm]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hN _) (Nat.cast_nonneg n))
    (abs_nonneg _)

theorem physicalRoughWalsh_power_bounds : ∃ N₀ > 0, ∀ (x₀ : d → ℝ) (ℓ h : ℝ),
    0 < ℓ → ℓ ≤ h → ∀ (x : d → ℝ) (n : ℕ),
      ‖Walsh.power (physicalRoughWalsh x₀ ℓ h x) n‖ ≤ N₀ ^ n ∧
      ∀ j : activeBlocks (d := d) ℓ h,
        ‖Walsh.symbolPart j (Walsh.power (physicalRoughWalsh x₀ ℓ h x) n)‖ ≤
          (n : ℝ) * N₀ ^ (n - 1) * |packet (coarseBump x₀ h) x₀ ℓ j.val x| := by
  obtain ⟨N₀, hN, hb⟩ := physicalRoughWalsh_bound (d := d)
  refine ⟨N₀, hN, fun x₀ ℓ h hℓ hℓh x n => ?_⟩
  have hn := hb x₀ ℓ h hℓ hℓh x
  exact ⟨(Walsh.power_norm _ n).trans (pow_le_pow_left₀ (norm_nonneg _) hn n),
    fun j => physicalRoughWalsh_power_symbol x₀ ℓ h x j n N₀ hn⟩

end CausalLowerbound.PartC

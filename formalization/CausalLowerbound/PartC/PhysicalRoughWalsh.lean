import CausalLowerbound.PartC.WalshRemoval
import CausalLowerbound.PartC.PhysicalRoughRegularity

/-! The actual finite rough field as an explicit Walsh coefficient array.
Its full coefficient norm is uniformly bounded and its single-symbol part is
exactly the corresponding localized physical packet. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry

variable {d : Type*} [Fintype d] [DecidableEq d]

def physicalRoughWalsh (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ) :
    Walsh.Coefficients (activeBlocks (d := d) ℓ h) :=
  ∑ k : activeBlocks (d := d) ℓ h,
    lp.single 1 {k} (physicalJitterWeights x₀ ℓ h 1 1 x k)

theorem physicalRoughWalsh_evaluate (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    Walsh.evaluate ζ (physicalRoughWalsh x₀ ℓ h x) = physicalRoughField x₀ ℓ h ζ x := by
  simp only [physicalRoughWalsh, map_sum, Walsh.evaluate_single, Walsh.character,
    Finset.prod_singleton, physicalRoughField, independentSignSum]

theorem physicalRoughWalsh_norm_le (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ) :
    ‖physicalRoughWalsh x₀ ℓ h x‖ ≤
      ∑ k : activeBlocks (d := d) ℓ h, |physicalJitterWeights x₀ ℓ h 1 1 x k| := by
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun k _ => by
    rw [lp.norm_single (by norm_num), Real.norm_eq_abs])

theorem physicalRoughWalsh_bound : ∃ N₀ > 0, ∀ (x₀ : d → ℝ) (ℓ h : ℝ),
    0 < ℓ → ℓ ≤ h → ∀ x : d → ℝ, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀ := by
  obtain ⟨N₀, hN, hb⟩ := physicalRough_packet_mass_bound (d := d)
  exact ⟨N₀, hN, fun x₀ ℓ h hℓ hℓh x =>
    (physicalRoughWalsh_norm_le x₀ ℓ h x).trans (hb x₀ ℓ h hℓ hℓh x)⟩

theorem physicalRoughWalsh_symbol (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ)
    (j : activeBlocks (d := d) ℓ h) :
    Walsh.symbolPart j (physicalRoughWalsh x₀ ℓ h x) =
      lp.single 1 {j} (physicalJitterWeights x₀ ℓ h 1 1 x j) := by
  simp [physicalRoughWalsh, Walsh.symbolPart, map_sum, Walsh.project_single]

theorem physicalRoughWalsh_symbol_norm (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ)
    (j : activeBlocks (d := d) ℓ h) :
    ‖Walsh.symbolPart j (physicalRoughWalsh x₀ ℓ h x)‖ =
      |packet (coarseBump x₀ h) x₀ ℓ j.val x| := by
  rw [physicalRoughWalsh_symbol, lp.norm_single (by norm_num), Real.norm_eq_abs]
  simp only [physicalJitterWeights, one_mul]

end CausalLowerbound.PartC

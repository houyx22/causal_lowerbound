import CausalLowerbound.PartC.AssignmentScaleChoice
import CausalLowerbound.PartC.NormalizedCarrierScales
import CausalLowerbound.PartC.PhysicalRoughWalsh

/-! One choice of normalization works for the actual Fourier assignment
multiplier and for every rough field. Constants precede all physical scales. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC
open Wiener PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem exists_normalized_assignment (η : ℝ) (hη : 0 < η) :
    ∃ c > 0, c ≤ 1 ∧ ∃ N₀ > 0, ∃ R > 0,
      (∀ (x₀ : d → ℝ) (ℓ h : ℝ), 0 < ℓ → ℓ ≤ h →
        ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) ∧
      ∀ t : ℝ, 0 < t → t ≤ 1 → ∃ w : ℝ, 0 < w ∧ w ≤ 1 / 2 ∧
        t ^ Fintype.card d / 4 ≤ w ∧ w ≤ t ^ Fintype.card d / 2 ∧
        N₀ / c ≤ carrierDegreeWeight R ((Fintype.card d : ℝ) * η) t ∧
        ∃ M : Fourier d, ‖M‖ ≤ carrierDegreeWeight R ((Fintype.card d : ℝ) * η) t ∧
          (∀ u ∈ Set.Icc (0 : d → ℝ) 1, toContinuous M (torusProjection u) =
            (assignmentMultiplier c w (fun i => 4 * u i - 2) : ℂ)) ∧
          ∀ x : d → ℝ, assignmentMultiplier c w x * linearPartition x = assignmentPartition w x ∧
            0 ≤ assignmentMultiplier c w x ∧ assignmentMultiplier c w x ≤ 1 / c := by
  obtain ⟨c, hc, hc1, C, hC, hb⟩ := exists_scaled_assignment_wiener (d := d) η hη
  obtain ⟨N₀, hN₀, hrough⟩ := physicalRoughWalsh_bound (d := d)
  let R := 1 + N₀ / c + C
  have hR : 0 < R := by dsimp [R]; positivity
  have hCN : N₀ / c ≤ R := by dsimp [R]; linarith
  have hCR : C ≤ R := by dsimp [R]; have := div_pos hN₀ hc; linarith
  refine ⟨c, hc, hc1, N₀, hN₀, R, hR, hrough, fun t ht ht1 => ?_⟩
  obtain ⟨m, _, hwlo, hwhi, hw1, M, hM, hMv, hm⟩ := hb t ht ht1
  refine ⟨dyadicWidth m, lt_of_lt_of_le (by positivity) hwlo, hw1, hwlo, hwhi, ?_, M, ?_, hMv, hm⟩
  · exact hCN.trans (carrierDegreeWeight_lower R _ t hR.le (by positivity) ht ht1)
  · exact hM.trans (mul_le_mul_of_nonneg_right hCR (Real.rpow_nonneg ht.le _))

end CausalLowerbound.PartC

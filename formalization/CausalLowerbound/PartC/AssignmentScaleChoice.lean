import CausalLowerbound.PartC.AssignmentMultiplierWiener
import CausalLowerbound.PartC.AssignmentTransition

/-! An actual dyadic assignment width at the physical transition scale
`t^d`, together with its Fourier multiplier and global volume bound. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace CausalLowerbound.PartC
open Wiener PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem assignment_width_rpow (t η : ℝ) (ht : 0 < t) :
    (t ^ Fintype.card d / 4) ^ (-η) =
      (4 : ℝ) ^ η * t ^ (-((Fintype.card d : ℝ) * η)) := by
  rw [Real.div_rpow (pow_nonneg ht.le _) (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul ht.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), div_inv_eq_mul]
  rw [show (Fintype.card d : ℝ) * -η = -((Fintype.card d : ℝ) * η) by ring]
  exact mul_comm _ _

theorem exists_scaled_assignment_wiener (η : ℝ) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ C ≥ 0, ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ N : ℕ, 0 < N ∧ t ^ Fintype.card d / 4 ≤ dyadicWidth N ∧
        dyadicWidth N ≤ t ^ Fintype.card d / 2 ∧ dyadicWidth N ≤ 1 / 2 ∧
        ∃ M : Fourier d, ‖M‖ ≤ C * t ^ (-((Fintype.card d : ℝ) * η)) ∧
          (∀ u ∈ Set.Icc (0 : d → ℝ) 1, toContinuous M (torusProjection u) =
            (assignmentMultiplier c (dyadicWidth N) (fun i => 4 * u i - 2) : ℂ)) ∧
          ∀ x : d → ℝ, assignmentMultiplier c (dyadicWidth N) x * linearPartition x =
            assignmentPartition (dyadicWidth N) x ∧
            0 ≤ assignmentMultiplier c (dyadicWidth N) x ∧
            assignmentMultiplier c (dyadicWidth N) x ≤ 1 / c := by
  obtain ⟨c, hc, hc1, C, hC, hb⟩ := exists_assignment_multiplier_wiener (d := d) η hη
  refine ⟨c, hc, hc1, C * (4 : ℝ) ^ η, by positivity, fun t ht ht1 => ?_⟩
  have hpow : t ^ Fintype.card d ≤ 1 := pow_le_one₀ ht.le ht1
  obtain ⟨N, hN, hlo, hu, M, hM, hvalue, hidentity⟩ :=
    hb (t ^ Fintype.card d / 4) (by positivity) (by linarith)
  have hw : dyadicWidth N ≤ t ^ Fintype.card d / 2 := by linarith
  refine ⟨N, hN, hlo, hw, by linarith, M, ?_, hvalue, hidentity⟩
  rw [assignment_width_rpow t η ht, ← mul_assoc] at hM
  exact hM

theorem active_assignmentTransition_rate_volume (t w : ℝ) (x₀ : d → ℝ) (r h : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hw : 0 < w) (hwt : w ≤ t ^ Fintype.card d)
    (hr : 0 < r) (hrh : r ≤ h) :
    volume (assignmentTransitionUnion (activeBlocks r h) w x₀ r) ≤ ENNReal.ofReal
      ((2 * Fintype.card d * (2 : ℝ) ^ (Fintype.card d - 1) * 7 ^ Fintype.card d) *
        h ^ Fintype.card d * t ^ Fintype.card d) := by
  have hw1 := hwt.trans (pow_le_one₀ ht.le ht1)
  apply (active_assignmentTransition_volume w x₀ r h hw hw1 hr hrh).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left hwt (by have hh := hr.trans_le hrh; positivity)

end CausalLowerbound.PartC

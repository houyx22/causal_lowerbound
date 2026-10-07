import CausalLowerbound.PartC.AssignmentPartitionWiener
import CausalLowerbound.PartC.AssignmentReciprocalWiener
import CausalLowerbound.PartC.DyadicPowerBound
import CausalLowerbound.PartC.DyadicSelection

/-! Actual Wiener realization of the smooth assignment multiplier.
Its norm loses at most an arbitrarily small inverse power of the chosen
transition width; no derivative or Fourier bound is an input. -/
noncomputable section
set_option autoImplicit false
namespace CausalLowerbound.PartC
open Wiener
variable {d : Type*} [Fintype d] [DecidableEq d]

def assignmentMultiplierWiener (c : ℝ) (hc : 0 < c) (N : ℕ) : Fourier d :=
  assignmentPartitionWiener N * assignmentReciprocalWiener c hc

theorem assignmentMultiplierWiener_value (c : ℝ) (hc : 0 < c) (N : ℕ)
    (u : d → ℝ) (hu : u ∈ Set.Icc 0 1) :
    toContinuous (assignmentMultiplierWiener (d := d) c hc N) (torusProjection u) =
      (assignmentMultiplier c (dyadicWidth N) (fun i => 4 * u i - 2) : ℂ) := by
  rw [assignmentMultiplierWiener, toContinuous_mul, ContinuousMap.mul_apply,
    assignmentPartitionWiener_value N u hu, assignmentReciprocalWiener_value c hc u hu]
  simp only [assignmentMultiplier, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]

theorem assignmentMultiplierWiener_polynomial_bound (c : ℝ) (hc : 0 < c) :
    ∃ C ≥ 0, ∀ N : ℕ, ‖assignmentMultiplierWiener (d := d) c hc N‖ ≤
      C * (N + 1 : ℝ) ^ Fintype.card d := by
  obtain ⟨C, hC, hb⟩ := assignmentPartitionWiener_bound (d := d)
  refine ⟨C * ‖assignmentReciprocalWiener (d := d) c hc‖, by positivity, fun N => ?_⟩
  calc
    _ ≤ ‖assignmentPartitionWiener (d := d) N‖ * ‖assignmentReciprocalWiener c hc‖ := norm_mul_le _ _
    _ ≤ (C * (N + 1 : ℝ) ^ Fintype.card d) * ‖assignmentReciprocalWiener c hc‖ :=
      mul_le_mul_of_nonneg_right (hb N) (norm_nonneg _)
    _ = _ := by ring

theorem assignmentMultiplierWiener_rpow_bound (c : ℝ) (hc : 0 < c) (η : ℝ) (hη : 0 < η) :
    ∃ C ≥ 0, ∀ N : ℕ,
      ‖assignmentMultiplierWiener (d := d) c hc N‖ ≤ C * (dyadicWidth N) ^ (-η) := by
  obtain ⟨C, hC, hb⟩ := assignmentMultiplierWiener_polynomial_bound (d := d) c hc
  obtain ⟨D, hD, hd⟩ := dyadic_polynomial_le_rpow (Fintype.card d) η hη
  refine ⟨C * D, mul_nonneg hC hD, fun N => ?_⟩
  calc
    _ ≤ C * (N + 1 : ℝ) ^ Fintype.card d := hb N
    _ ≤ C * (D * (dyadicWidth N) ^ (-η)) := mul_le_mul_of_nonneg_left (hd N) hC
    _ = _ := (mul_assoc _ _ _).symm

/-- One fixed positive reciprocal threshold works for all requested widths.
The returned width lies between the request and twice the request, and
the Fourier element realizes the exact smooth multiplier on the chart. -/
theorem exists_assignment_multiplier_wiener (η : ℝ) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ C ≥ 0, ∀ w : ℝ, 0 < w → w ≤ 1 / 4 →
      ∃ N : ℕ, 0 < N ∧ w ≤ dyadicWidth N ∧ dyadicWidth N < 2 * w ∧
        ∃ A : Fourier d, ‖A‖ ≤ C * w ^ (-η) ∧
          (∀ u ∈ Set.Icc (0 : d → ℝ) 1, toContinuous A (torusProjection u) =
            (assignmentMultiplier c (dyadicWidth N) (fun i => 4 * u i - 2) : ℂ)) ∧
          ∀ x : d → ℝ, assignmentMultiplier c (dyadicWidth N) x * linearPartition x =
            assignmentPartition (dyadicWidth N) x ∧
            0 ≤ assignmentMultiplier c (dyadicWidth N) x ∧
            assignmentMultiplier c (dyadicWidth N) x ≤ 1 / c := by
  obtain ⟨c, hc, hc1, hm⟩ := exists_assignmentMultiplier (d := d)
  obtain ⟨C, hC, hb⟩ := assignmentMultiplierWiener_rpow_bound (d := d) c hc η hη
  refine ⟨c, hc, hc1, C, hC, fun w hw hw1 => ?_⟩
  obtain ⟨N, hN, hlow, hu, hu1⟩ := exists_dyadic_width w hw hw1
  refine ⟨N, hN, hlow, hu, assignmentMultiplierWiener c hc N, ?_,
    fun u hu => assignmentMultiplierWiener_value c hc N u hu, ?_⟩
  · exact (hb N).trans (mul_le_mul_of_nonneg_left (dyadicWidth_rpow_le N w η hw hη.le hlow) hC)
  · exact (hm (dyadicWidth N) (dyadicWidth_pos N) hu1).2.2

end CausalLowerbound.PartC

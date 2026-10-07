import CausalLowerbound.PartC.AssignmentWindowWiener
import CausalLowerbound.PartC.AssignmentPartition
import CausalLowerbound.WienerCoordinate
import CausalLowerbound.WienerTensor

/-! Tensorization of the actual one-dimensional window realization.
There is one factor per physical coordinate, so the dyadic-depth loss
is a polynomial of degree equal to the dimension. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace CausalLowerbound.PartC
open Wiener
variable {d : Type*} [Fintype d] [DecidableEq d]

def assignmentPartitionWiener (N : ℕ) : Fourier d :=
  ∏ i, liftCoordinate i (assignmentWindowWiener N)

theorem assignmentPartitionWiener_value (N : ℕ) (u : d → ℝ) (hu : u ∈ Set.Icc 0 1) :
    toContinuous (assignmentPartitionWiener (d := d) N) (torusProjection u) =
      (assignmentPartition (dyadicWidth N) (fun i => 4 * u i - 2) : ℂ) := by
  simp only [assignmentPartitionWiener, toContinuous_prod, ContinuousMap.prod_apply,
    liftCoordinate_value, assignmentPartition, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact assignmentWindowWiener_value N (u i) ⟨hu.1 i, hu.2 i⟩

theorem assignmentPartitionWiener_bound : ∃ C ≥ 0, ∀ N : ℕ,
    ‖assignmentPartitionWiener (d := d) N‖ ≤ C * (N + 1 : ℝ) ^ Fintype.card d := by
  obtain ⟨C, hC, hb⟩ := assignmentWindowWiener_bound
  refine ⟨C ^ Fintype.card d, pow_nonneg hC _, fun N => ?_⟩
  calc
    _ ≤ ∏ i : d, ‖liftCoordinate i (assignmentWindowWiener N)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _i : d, C * (N + 1 : ℝ) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun i hi => (liftCoordinate_norm i _).trans (hb N))
    _ = C ^ Fintype.card d * (N + 1 : ℝ) ^ Fintype.card d := by simp [mul_pow]

end CausalLowerbound.PartC

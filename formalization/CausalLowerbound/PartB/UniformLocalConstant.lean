import CausalLowerbound.PartB.PhysicalLocalHellinger

/-! One finite information constant works for every component size
at most Q. It is independent of sample size and perturbation amplitude. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt

def localInformationCoefficient (κ : ℝ) (m : ℕ) : ℝ :=
  (Fintype.card (Fin m → Bool × Bool) : ℝ) * (componentStabilityConstant m) ^ 2 / (κ ^ 2) ^ m

def uniformInformationConstant (κ : ℝ) (Q : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (Q + 1), localInformationCoefficient κ m

theorem localInformationCoefficient_nonneg (κ : ℝ) (m : ℕ) : 0 ≤ localInformationCoefficient κ m := by
  unfold localInformationCoefficient
  positivity

theorem uniformInformationConstant_nonneg (κ : ℝ) (Q : ℕ) : 0 ≤ uniformInformationConstant κ Q :=
  Finset.sum_nonneg (fun m _ => localInformationCoefficient_nonneg κ m)

theorem localInformationCoefficient_le (κ : ℝ) (Q m : ℕ) (hm : m ≤ Q) :
    localInformationCoefficient κ m ≤ uniformInformationConstant κ Q :=
  Finset.single_le_sum (fun i _ => localInformationCoefficient_nonneg κ i)
    (Finset.mem_range.mpr (by omega))

theorem localInformation_prefactor_le (κ δ : ℝ) (Q m : ℕ) (hm : m ≤ Q) :
    (Fintype.card (Fin m → Bool × Bool) : ℝ) * (componentStabilityConstant m * δ) ^ 2 / (κ ^ 2) ^ m ≤
      uniformInformationConstant κ Q * δ ^ 2 := by
  have hh := mul_le_mul_of_nonneg_right (localInformationCoefficient_le κ Q m hm) (sq_nonneg δ)
  convert hh using 1
  unfold localInformationCoefficient
  ring

end CausalLowerbound.PartB.ShellGeometry

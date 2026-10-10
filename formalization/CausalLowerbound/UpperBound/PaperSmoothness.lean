import CausalLowerbound.UpperBound.RealOutcomeModel
import Mathlib.Algebra.Order.Floor.Semiring

/-! The paper's convention q = ceil(a) - 1, theta = a - q.
In particular, positive integer smoothness m means m-1 derivatives with
a Lipschitz top derivative, rather than an extra continuous derivative. -/

noncomputable section
set_option autoImplicit false
open Set

namespace CausalLowerbound.UpperBound

def smoothnessOrder (a : ℝ) : ℕ := Nat.ceil a - 1

def smoothnessFraction (a : ℝ) : ℝ := a - smoothnessOrder a

theorem smoothnessFraction_pos {a : ℝ} (ha : 0 < a) : 0 < smoothnessFraction a := by
  unfold smoothnessFraction
  apply sub_pos.mpr
  apply Nat.lt_ceil.mp
  exact Nat.sub_lt (Nat.ceil_pos.mpr ha) (by norm_num)

theorem smoothnessFraction_le_one {a : ℝ} (ha : 0 < a) : smoothnessFraction a ≤ 1 := by
  have hc : 1 ≤ Nat.ceil a := Nat.ceil_pos.mpr ha
  have he : a ≤ (Nat.ceil a : ℝ) := Nat.ceil_le.mp (le_refl _)
  unfold smoothnessFraction smoothnessOrder
  rw [Nat.cast_sub hc, Nat.cast_one]
  linarith

@[simp] theorem smoothness_reconstruct (a : ℝ) : (smoothnessOrder a : ℝ) + smoothnessFraction a = a := by
  unfold smoothnessFraction
  ring

theorem smoothnessOrder_integer (m : ℕ) : smoothnessOrder (m : ℝ) = m - 1 := by
  simp [smoothnessOrder]

theorem smoothnessFraction_integer {m : ℕ} (hm : 0 < m) : smoothnessFraction (m : ℝ) = 1 := by
  unfold smoothnessFraction
  rw [smoothnessOrder_integer, Nat.cast_sub hm, Nat.cast_one]
  ring

namespace RealOutcomeModel

variable {d : Type*} [Fintype d] {ε lower upper M₂ : ℝ}

def PaperRegularity (M : RealOutcomeModel d ε lower upper M₂) (U : Set (d → ℝ))
    (α β γ Lπ L₀ Lτ : ℝ) : Prop :=
  M.LocalRegularity U (smoothnessOrder α) (smoothnessOrder β) (smoothnessOrder γ)
    (smoothnessFraction α) (smoothnessFraction β) (smoothnessFraction γ) Lπ L₀ Lτ

end RealOutcomeModel
end CausalLowerbound.UpperBound

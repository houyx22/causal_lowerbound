import CausalLowerbound.PartC.AssignmentWindow

/-! Exact dyadic decomposition of the narrowing assignment windows.
Each layer is a difference of two rescalings of one fixed compact smooth
profile; this is the input to the uniform Wiener estimate. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators
namespace CausalLowerbound.PartC

def assignmentLayer (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1 / 2) - Real.smoothTransition (x / 2 + 1 / 2)

theorem assignmentLayer_smooth : ContDiff ℝ ∞ assignmentLayer :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    (Real.smoothTransition.contDiff.comp ((contDiff_id.div_const 2).add contDiff_const))

theorem assignmentLayer_zero (x : ℝ) (hx : 1 ≤ |x|) : assignmentLayer x = 0 := by
  rcases le_abs.mp hx with h | h
  · have ha : 1 ≤ x + 1 / 2 := by linarith
    have hb : 1 ≤ x / 2 + 1 / 2 := by linarith
    simp only [assignmentLayer, Real.smoothTransition.one_of_one_le ha,
      Real.smoothTransition.one_of_one_le hb, sub_self]
  · have ha : x + 1 / 2 ≤ 0 := by linarith
    have hb : x / 2 + 1 / 2 ≤ 0 := by linarith
    simp only [assignmentLayer, Real.smoothTransition.zero_of_nonpos ha,
      Real.smoothTransition.zero_of_nonpos hb, sub_self]

theorem assignmentLayer_support (x : ℝ) (hx : assignmentLayer x ≠ 0) : |x| < 1 :=
  lt_of_not_ge (fun h => hx (assignmentLayer_zero x h))

theorem assignmentLayer_compact : HasCompactSupport assignmentLayer := by
  have hh : tsupport assignmentLayer ⊆ Set.Icc (-1) 1 := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    exact abs_le.mp (assignmentLayer_support x hx).le
  exact isCompact_Icc.of_isClosed_subset isClosed_closure hh

theorem assignmentWindow_layer (w x : ℝ) :
    assignmentWindow w x - assignmentWindow (2 * w) x =
      assignmentLayer ((x + 1 / 2) / w) - assignmentLayer ((x - 1 / 2) / w) := by
  have h (y : ℝ) : y / (2 * w) = (y / w) / 2 := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp only [assignmentWindow, assignmentLayer, h]
  ring

def dyadicWidth (N : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ N

theorem dyadicWidth_pos (N : ℕ) : 0 < dyadicWidth N := by
  unfold dyadicWidth
  positivity

theorem dyadicWidth_le_one (N : ℕ) : dyadicWidth N ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

@[simp] theorem dyadicWidth_zero : dyadicWidth 0 = 1 := by simp [dyadicWidth]

theorem dyadicWidth_succ (N : ℕ) : 2 * dyadicWidth (N + 1) = dyadicWidth N := by
  simp only [dyadicWidth, pow_succ]
  ring

theorem dyadicWidth_inverse (N : ℕ) : (dyadicWidth N)⁻¹ = (2 : ℝ) ^ N := by
  simp [dyadicWidth]

theorem assignmentWindow_dyadic_step (N : ℕ) (x : ℝ) :
    assignmentWindow (dyadicWidth (N + 1)) x - assignmentWindow (dyadicWidth N) x =
      assignmentLayer ((x + 1 / 2) / dyadicWidth (N + 1)) -
        assignmentLayer ((x - 1 / 2) / dyadicWidth (N + 1)) := by
  simpa only [dyadicWidth_succ] using assignmentWindow_layer (dyadicWidth (N + 1)) x

theorem assignmentWindow_dyadic_sum (N : ℕ) (x : ℝ) :
    assignmentWindow (dyadicWidth N) x = assignmentWindow 1 x +
      ∑ j ∈ Finset.range N, (assignmentLayer ((x + 1 / 2) / dyadicWidth (j + 1)) -
        assignmentLayer ((x - 1 / 2) / dyadicWidth (j + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← sub_eq_iff_eq_add.mpr ih]
    linarith [assignmentWindow_dyadic_step N x]

end CausalLowerbound.PartC

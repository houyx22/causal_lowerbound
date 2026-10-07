import CausalLowerbound.SmoothWindow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! A narrow smooth assignment window built from a difference of smooth
steps. This avoids constructing a convolution with an interval indicator.
For `0 < w ≤ 1` its translates form the same adjacent partition pattern
as `smoothWindow`, with transition intervals of length `w`. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace CausalLowerbound.PartC

def assignmentWindow (w x : ℝ) : ℝ :=
  Real.smoothTransition ((x + 1 / 2) / w + 1 / 2) -
    Real.smoothTransition ((x - 1 / 2) / w + 1 / 2)

theorem assignmentWindow_smooth (w : ℝ) : ContDiff ℝ ∞ (assignmentWindow w) :=
  (Real.smoothTransition.contDiff.comp
    (((contDiff_id.add contDiff_const).div_const w).add contDiff_const)).sub
    (Real.smoothTransition.contDiff.comp
      (((contDiff_id.sub contDiff_const).div_const w).add contDiff_const))

theorem assignmentWindow_left (w x : ℝ) (hw : 0 < w) (hx : x ≤ -(1 + w) / 2) :
    assignmentWindow w x = 0 := by
  have ha : (x + 1 / 2) / w + 1 / 2 ≤ 0 := by
    have hh := (div_le_iff₀ hw).mpr (show x + 1 / 2 ≤ (-1 / 2) * w by linarith)
    linarith
  have hb : (x - 1 / 2) / w + 1 / 2 ≤ 0 := by
    have hh := (div_le_iff₀ hw).mpr (show x - 1 / 2 ≤ (-1 / 2) * w by linarith)
    linarith
  simp only [assignmentWindow, Real.smoothTransition.zero_of_nonpos ha,
    Real.smoothTransition.zero_of_nonpos hb, sub_self]

theorem assignmentWindow_right (w x : ℝ) (hw : 0 < w) (hx : (1 + w) / 2 ≤ x) :
    assignmentWindow w x = 0 := by
  have ha : 1 ≤ (x + 1 / 2) / w + 1 / 2 := by
    have hh := (le_div_iff₀ hw).mpr (show (1 / 2) * w ≤ x + 1 / 2 by linarith)
    linarith
  have hb : 1 ≤ (x - 1 / 2) / w + 1 / 2 := by
    have hh := (le_div_iff₀ hw).mpr (show (1 / 2) * w ≤ x - 1 / 2 by linarith)
    linarith
  simp only [assignmentWindow, Real.smoothTransition.one_of_one_le ha,
    Real.smoothTransition.one_of_one_le hb, sub_self]

theorem assignmentWindow_plateau (w x : ℝ) (hw : 0 < w)
    (hx : -(1 - w) / 2 ≤ x ∧ x ≤ (1 - w) / 2) : assignmentWindow w x = 1 := by
  have ha : 1 ≤ (x + 1 / 2) / w + 1 / 2 := by
    have hh := (le_div_iff₀ hw).mpr (show (1 / 2) * w ≤ x + 1 / 2 by linarith [hx.1])
    linarith
  have hb : (x - 1 / 2) / w + 1 / 2 ≤ 0 := by
    have hh := (div_le_iff₀ hw).mpr (show x - 1 / 2 ≤ (-1 / 2) * w by linarith [hx.2])
    linarith
  simp only [assignmentWindow, Real.smoothTransition.one_of_one_le ha,
    Real.smoothTransition.zero_of_nonpos hb, sub_zero]

theorem assignmentWindow_bounds (w x : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) :
    0 ≤ assignmentWindow w x ∧ assignmentWindow w x ≤ 1 := by
  have hgap : (x + 1 / 2) / w + 1 / 2 - ((x - 1 / 2) / w + 1 / 2) = 1 / w := by ring
  have hstep : 1 ≤ 1 / w := (le_div_iff₀ hw).mpr (by simpa using hw1)
  constructor
  · by_cases hb : (x - 1 / 2) / w + 1 / 2 ≤ 0
    · rw [assignmentWindow, Real.smoothTransition.zero_of_nonpos hb, sub_zero]
      exact Real.smoothTransition.nonneg _
    · have ha : 1 ≤ (x + 1 / 2) / w + 1 / 2 := by linarith
      rw [assignmentWindow, Real.smoothTransition.one_of_one_le ha]
      exact sub_nonneg.mpr (Real.smoothTransition.le_one _)
  · unfold assignmentWindow
    linarith [Real.smoothTransition.le_one ((x + 1 / 2) / w + 1 / 2),
      Real.smoothTransition.nonneg ((x - 1 / 2) / w + 1 / 2)]

theorem assignmentWindow_support (w x : ℝ) (hw : 0 < w) (hx : assignmentWindow w x ≠ 0) :
    -(1 + w) / 2 < x ∧ x < (1 + w) / 2 :=
  ⟨lt_of_not_ge (fun h => hx (assignmentWindow_left w x hw h)),
    lt_of_not_ge (fun h => hx (assignmentWindow_right w x hw h))⟩

theorem assignmentWindow_compact (w : ℝ) (hw : 0 < w) : HasCompactSupport (assignmentWindow w) := by
  have hh : tsupport (assignmentWindow w) ⊆ Set.Icc (-(1 + w) / 2) ((1 + w) / 2) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    exact ⟨(assignmentWindow_support w x hw hx).1.le, (assignmentWindow_support w x hw hx).2.le⟩
  exact isCompact_Icc.of_isClosed_subset isClosed_closure hh

theorem assignmentWindow_pair (w x : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (hx : x ∈ Set.Icc 0 1) : assignmentWindow w x + assignmentWindow w (x - 1) = 1 := by
  have ha : 1 ≤ (x + 1 / 2) / w + 1 / 2 := by
    have hh := (le_div_iff₀ hw).mpr (show (1 / 2) * w ≤ x + 1 / 2 by linarith [hx.1])
    linarith
  have hb : (x - 1 - 1 / 2) / w + 1 / 2 ≤ 0 := by
    have hh := (div_le_iff₀ hw).mpr (show x - 1 - 1 / 2 ≤ (-1 / 2) * w by linarith [hx.2])
    linarith
  have hm : (x - 1 + 1 / 2) / w + 1 / 2 = (x - 1 / 2) / w + 1 / 2 := by ring
  simp only [assignmentWindow, ha, Real.smoothTransition.one_of_one_le ha,
    Real.smoothTransition.zero_of_nonpos hb, hm]
  ring

theorem assignmentWindow_integer_zero (w x : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (hx : x ∈ Set.Icc 0 1) (k : ℤ) (hk : k ∉ ({0, -1} : Finset ℤ)) :
    assignmentWindow w (x + k) = 0 := by
  have hk' : k ≠ 0 ∧ k ≠ -1 := by simpa using hk
  by_cases h : 0 ≤ k
  · have hi : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    exact assignmentWindow_right w _ hw (by linarith [hx.1])
  · have hi : (k : ℝ) ≤ -2 := by exact_mod_cast (show k ≤ -2 by omega)
    exact assignmentWindow_left w _ hw (by linarith [hx.2])

end CausalLowerbound.PartC

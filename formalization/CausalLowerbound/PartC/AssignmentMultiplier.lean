import CausalLowerbound.PartC.AssignmentPartition

/-! A globally smooth reciprocal extension. The assignment multiplier is
well defined even outside the support of the carried partition; on the
assignment support it is the exact quotient required by the site shift. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace CausalLowerbound.PartC

def positiveFloor (c y : ℝ) : ℝ :=
  c / 2 + (y - c / 2) * Real.smoothTransition ((y - c / 2) / (c / 2))

theorem positiveFloor_smooth (c : ℝ) : ContDiff ℝ ∞ (positiveFloor c) :=
  contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (c / 2))))

theorem positiveFloor_lower (c y : ℝ) (hc : 0 < c) : c / 2 ≤ positiveFloor c y := by
  by_cases hy : c / 2 ≤ y
  · have hh := mul_nonneg (sub_nonneg.mpr hy)
      (Real.smoothTransition.nonneg ((y - c / 2) / (c / 2)))
    unfold positiveFloor
    linarith
  · have ha : (y - c / 2) / (c / 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    simp [positiveFloor, Real.smoothTransition.zero_of_nonpos ha]

theorem positiveFloor_pos (c y : ℝ) (hc : 0 < c) : 0 < positiveFloor c y :=
  (half_pos hc).trans_le (positiveFloor_lower c y hc)

theorem positiveFloor_eq (c y : ℝ) (hc : 0 < c) (hy : c ≤ y) : positiveFloor c y = y := by
  have ha : 1 ≤ (y - c / 2) / (c / 2) := (le_div_iff₀ (half_pos hc)).mpr (by linarith)
  rw [positiveFloor, Real.smoothTransition.one_of_one_le ha]
  ring

variable {d : Type*} [Fintype d]

def assignmentMultiplier (c w : ℝ) (x : d → ℝ) : ℝ :=
  assignmentPartition w x / positiveFloor c (linearPartition x)

theorem assignmentMultiplier_smooth (c w : ℝ) (hc : 0 < c) :
    ContDiff ℝ ∞ (assignmentMultiplier (d := d) c w) :=
  (assignmentPartition_smooth w).div
    ((positiveFloor_smooth c).comp linearPartition_smooth)
    (fun x => (positiveFloor_pos c (linearPartition x) hc).ne')

theorem assignmentMultiplier_support (c w : ℝ) :
    tsupport (assignmentMultiplier (d := d) c w) ⊆ tsupport (assignmentPartition w) := by
  change tsupport (fun x : d → ℝ => assignmentPartition w x / positiveFloor c (linearPartition x)) ⊆ _
  simp only [div_eq_mul_inv]
  exact tsupport_mul_subset_left

theorem assignmentMultiplier_compact (c w : ℝ) (hw : 0 < w) :
    HasCompactSupport (assignmentMultiplier (d := d) c w) :=
  (assignmentPartition_compact w hw).of_isClosed_subset isClosed_closure (assignmentMultiplier_support c w)

theorem assignmentMultiplier_identity (c w : ℝ) (hc : 0 < c)
    (hlower : ∀ x ∈ tsupport (assignmentPartition (d := d) w), c ≤ linearPartition x) (x : d → ℝ) :
    assignmentMultiplier c w x * linearPartition x = assignmentPartition w x := by
  by_cases hx : assignmentPartition w x = 0
  · simp [assignmentMultiplier, hx]
  · have hl := hlower x (subset_closure hx)
    have hpos : 0 < linearPartition x := hc.trans_le hl
    rw [assignmentMultiplier, positiveFloor_eq c _ hc hl]
    exact div_mul_cancel₀ _ hpos.ne'

theorem assignmentMultiplier_bounds (c w : ℝ) (hc : 0 < c) (hw : 0 < w) (hw1 : w ≤ 1)
    (hlower : ∀ x ∈ tsupport (assignmentPartition (d := d) w), c ≤ linearPartition x) (x : d → ℝ) :
    0 ≤ assignmentMultiplier c w x ∧ assignmentMultiplier c w x ≤ 1 / c := by
  have hb := assignmentPartition_bounds w hw hw1 x
  refine ⟨div_nonneg hb.1 (positiveFloor_pos c (linearPartition x) hc).le, ?_⟩
  by_cases hx : assignmentPartition w x = 0
  · simp only [assignmentMultiplier, hx, zero_div]
    positivity
  · have hl := hlower x (subset_closure hx)
    have hpos : 0 < linearPartition x := hc.trans_le hl
    rw [assignmentMultiplier, positiveFloor_eq c _ hc hl]
    apply (div_le_iff₀ hpos).mpr
    have hratio : 1 ≤ linearPartition x / c := (le_div_iff₀ hc).mpr (by simpa using hl)
    have h := hb.2.trans hratio
    simpa [div_eq_mul_inv, mul_comm] using h

theorem exists_assignmentMultiplier :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (w : ℝ), 0 < w → w ≤ 1 / 2 →
      ContDiff ℝ ∞ (assignmentMultiplier (d := d) c w) ∧
      HasCompactSupport (assignmentMultiplier (d := d) c w) ∧
      ∀ x : d → ℝ, assignmentMultiplier c w x * linearPartition x = assignmentPartition w x ∧
        0 ≤ assignmentMultiplier c w x ∧ assignmentMultiplier c w x ≤ 1 / c := by
  obtain ⟨c, hc, hc1, hbound⟩ := assignmentPartition_carried_lower_bound (d := d)
  refine ⟨c, hc, hc1, fun w hw hw1 => ⟨assignmentMultiplier_smooth c w hc,
    assignmentMultiplier_compact c w hw, fun x => ⟨?_, ?_⟩⟩⟩
  · exact assignmentMultiplier_identity c w hc (hbound w hw hw1) x
  · exact assignmentMultiplier_bounds c w hc hw (by linarith) (hbound w hw hw1) x

end CausalLowerbound.PartC

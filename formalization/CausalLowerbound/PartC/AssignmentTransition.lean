import CausalLowerbound.PartC.AssignmentPartition
import CausalLowerbound.PartB.ClusterVolume
import CausalLowerbound.PartB.CarrierCounting

/-! The actual assignment transition layer has volume proportional to its
width, uniformly in the physical carrier scale and the number of blocks. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def assignmentTransition (w : ℝ) (x₀ : d → ℝ) (r : ℝ) : Set (d → ℝ) :=
  {x | rescaled (assignmentPartition w) x₀ r x ≠ 0 ∧
    rescaled (assignmentPartition w) x₀ r x ≠ 1}

theorem assignmentTransition_measurable (w : ℝ) (x₀ : d → ℝ) (r : ℝ) :
    MeasurableSet (assignmentTransition w x₀ r) := by
  have hc := (rescaled_smooth _ (assignmentPartition_smooth w) x₀ r).continuous
  exact (isClosed_eq hc continuous_const).measurableSet.compl.inter
    (isClosed_eq hc continuous_const).measurableSet.compl

theorem assignmentTransition_subset (w : ℝ) (x₀ : d → ℝ) (r : ℝ)
    (hw : 0 < w) (hr : 0 < r) :
    assignmentTransition w x₀ r ⊆
      coordinateBox x₀ (r * (1 + w) / 2) \ coordinateBox x₀ (r * (1 - w) / 2) := by
  intro x hx
  have he : r⁻¹ • (x - x₀) = (fun i => (x i - x₀ i) / r) := by
    funext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hx' : assignmentPartition w (fun i => (x i - x₀ i) / r) ≠ 0 ∧
      assignmentPartition w (fun i => (x i - x₀ i) / r) ≠ 1 := by
    simpa only [assignmentTransition, Set.mem_setOf_eq, rescaled, he] using hx
  have hu := assignmentPartition_support w hw (subset_closure hx'.1)
  refine ⟨?_, ?_⟩
  · apply (mem_coordinateBox _ _ _).mpr
    intro i
    have hl := (le_div_iff₀ hr).mp (hu.1 i)
    have hh := (div_le_iff₀ hr).mp (hu.2 i)
    rw [abs_le]
    constructor <;> nlinarith
  · intro hi
    apply hx'.2
    apply assignmentPartition_plateau w hw
    have hi' := (mem_coordinateBox _ _ _).mp hi
    constructor <;> intro i
    · apply (le_div_iff₀ hr).mpr
      have hh := (abs_le.mp (hi' i)).1
      linarith
    · apply (div_le_iff₀ hr).mpr
      have hh := (abs_le.mp (hi' i)).2
      linarith

theorem assignment_power_gap (N : ℕ) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    (1 + w) ^ N - (1 - w) ^ N ≤ (2 * N * (2 : ℝ) ^ (N - 1)) * w := by
  have hb := abs_pow_sub_pow_le (1 + w) (1 - w) N
  rw [abs_of_nonneg (by linarith : 0 ≤ 1 + w),
    abs_of_nonneg (by linarith : 0 ≤ 1 - w), max_eq_left (by linarith),
    show (1 + w) - (1 - w) = 2 * w by ring, abs_of_nonneg (by positivity : 0 ≤ 2 * w)] at hb
  calc
    _ ≤ |(1 + w) ^ N - (1 - w) ^ N| := le_abs_self _
    _ ≤ (2 * w) * N * (1 + w) ^ (N - 1) := hb
    _ ≤ (2 * w) * N * (2 : ℝ) ^ (N - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) _) (by positivity)
    _ = _ := by ring

theorem assignmentTransition_volume (w : ℝ) (x₀ : d → ℝ) (r : ℝ)
    (hw : 0 < w) (hw1 : w ≤ 1) (hr : 0 < r) :
    volume (assignmentTransition w x₀ r) ≤
      ENNReal.ofReal ((2 * Fintype.card d * (2 : ℝ) ^ (Fintype.card d - 1)) * r ^ Fintype.card d * w) := by
  have hsub : coordinateBox x₀ (r * (1 - w) / 2) ⊆ coordinateBox x₀ (r * (1 + w) / 2) := by
    intro x hx
    apply (mem_coordinateBox _ _ _).mpr
    intro i
    exact ((mem_coordinateBox _ _ _).mp hx i).trans (by nlinarith)
  have hfin : volume (coordinateBox x₀ (r * (1 - w) / 2)) ≠ ⊤ := by
    rw [coordinateBox_volume]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  apply (measure_mono (assignmentTransition_subset w x₀ r hw hr)).trans
  rw [measure_diff hsub measurableSet_Icc.nullMeasurableSet hfin,
    coordinateBox_volume, coordinateBox_volume,
    show 2 * (r * (1 + w) / 2) = r * (1 + w) by ring,
    show 2 * (r * (1 - w) / 2) = r * (1 - w) by ring,
    ← ENNReal.ofReal_pow (mul_nonneg hr.le (by linarith)) _,
    ← ENNReal.ofReal_pow (mul_nonneg hr.le (by linarith)) _,
    ← ENNReal.ofReal_sub _ (pow_nonneg (mul_nonneg hr.le (by linarith)) _)]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_pow, mul_pow, ← mul_sub]
  calc
    _ ≤ r ^ Fintype.card d * ((2 * Fintype.card d * (2 : ℝ) ^ (Fintype.card d - 1)) * w) :=
      mul_le_mul_of_nonneg_left (assignment_power_gap _ w hw.le hw1) (pow_nonneg hr.le _)
    _ = _ := by ring

def assignmentTransitionUnion (S : Finset (d → ℤ)) (w : ℝ) (x₀ : d → ℝ) (r : ℝ) : Set (d → ℝ) :=
  ⋃ k ∈ S, assignmentTransition w (packetCenter x₀ r k) r

theorem assignmentTransitionUnion_measurable (S : Finset (d → ℤ)) (w : ℝ)
    (x₀ : d → ℝ) (r : ℝ) : MeasurableSet (assignmentTransitionUnion S w x₀ r) :=
  MeasurableSet.iUnion (fun k => MeasurableSet.iUnion
    (fun _hk => assignmentTransition_measurable w (packetCenter x₀ r k) r))

theorem assignmentTransitionUnion_volume (S : Finset (d → ℤ)) (w : ℝ) (x₀ : d → ℝ) (r : ℝ)
    (hw : 0 < w) (hw1 : w ≤ 1) (hr : 0 < r) :
    volume (assignmentTransitionUnion S w x₀ r) ≤ ENNReal.ofReal
      ((S.card : ℝ) * (2 * Fintype.card d * (2 : ℝ) ^ (Fintype.card d - 1)) * r ^ Fintype.card d * w) := by
  calc
    _ ≤ ∑ k ∈ S, volume (assignmentTransition w (packetCenter x₀ r k) r) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ S, ENNReal.ofReal
        ((2 * Fintype.card d * (2 : ℝ) ^ (Fintype.card d - 1)) * r ^ Fintype.card d * w) :=
      Finset.sum_le_sum (fun k hk => assignmentTransition_volume w _ r hw hw1 hr)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)]
      congr 1
      ring

theorem active_assignmentTransition_volume (w : ℝ) (x₀ : d → ℝ) (r h : ℝ)
    (hw : 0 < w) (hw1 : w ≤ 1) (hr : 0 < r) (hrh : r ≤ h) :
    volume (assignmentTransitionUnion (activeBlocks r h) w x₀ r) ≤ ENNReal.ofReal
      ((2 * Fintype.card d * (2 : ℝ) ^ (Fintype.card d - 1) * 7 ^ Fintype.card d) *
        h ^ Fintype.card d * w) := by
  apply (assignmentTransitionUnion_volume _ w x₀ r hw hw1 hr).trans
  apply ENNReal.ofReal_le_ofReal
  have hb := activeBlocks_card_bound (d := d) r h hr hrh
  have he : (7 * (h / r)) ^ Fintype.card d * r ^ Fintype.card d = (7 * h) ^ Fintype.card d := by
    rw [← mul_pow]
    congr 1
    field_simp [hr.ne']
  calc
    _ ≤ (7 * (h / r)) ^ Fintype.card d *
        (2 * Fintype.card d * (2 : ℝ) ^ (Fintype.card d - 1)) * r ^ Fintype.card d * w := by
      gcongr
    _ = (2 * Fintype.card d * (2 : ℝ) ^ (Fintype.card d - 1)) *
        ((7 * (h / r)) ^ Fintype.card d * r ^ Fintype.card d) * w := by ring
    _ = _ := by rw [he, mul_pow]; ring

end CausalLowerbound.PartC

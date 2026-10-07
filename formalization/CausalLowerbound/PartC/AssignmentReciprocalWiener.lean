import CausalLowerbound.PartC.AssignmentMultiplier
import CausalLowerbound.CompactChartWiener

/-! The reciprocal of the carried partition on the assignment support
extends to a fixed smooth torus function. Its Wiener norm is independent
of the assignment width. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace CausalLowerbound.PartC
open Wiener
variable {d : Type*} [Fintype d]

theorem positiveFloor_zero (c : ℝ) (hc : 0 < c) : positiveFloor c 0 = c / 2 := by
  have ha : (0 - c / 2) / (c / 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  rw [positiveFloor, Real.smoothTransition.zero_of_nonpos ha, mul_zero, add_zero]

def reciprocalCorrection (c : ℝ) (x : d → ℝ) : ℂ :=
  (((positiveFloor c (linearPartition x))⁻¹ - (c / 2)⁻¹ : ℝ) : ℂ)

theorem reciprocalCorrection_smooth (c : ℝ) (hc : 0 < c) :
    ContDiff ℝ ∞ (reciprocalCorrection (d := d) c) :=
  Complex.ofRealCLM.contDiff.comp
    ((((positiveFloor_smooth c).comp linearPartition_smooth).inv
      (fun x => (positiveFloor_pos c (linearPartition x) hc).ne')).sub contDiff_const)

theorem reciprocalCorrection_support (c : ℝ) (hc : 0 < c) :
    Function.support (reciprocalCorrection (d := d) c) ⊆ Function.support linearPartition := by
  intro x hx
  change linearPartition x ≠ 0
  intro hz
  apply hx
  simp only [reciprocalCorrection, hz, positiveFloor_zero c hc, sub_self, Complex.ofReal_zero]

theorem reciprocalCorrection_compact (c : ℝ) (hc : 0 < c) :
    HasCompactSupport (reciprocalCorrection (d := d) c) :=
  linearPartition_compact.mono (reciprocalCorrection_support c hc)

def assignmentReciprocalWiener (c : ℝ) (hc : 0 < c) : Fourier d :=
  (c / 2)⁻¹ • (1 : Fourier d) +
    compactChartWiener (reciprocalCorrection c) (reciprocalCorrection_compact c hc)
      (reciprocalCorrection_smooth c hc)

theorem assignmentReciprocalWiener_value (c : ℝ) (hc : 0 < c)
    (u : d → ℝ) (hu : u ∈ Set.Icc 0 1) :
    toContinuous (assignmentReciprocalWiener (d := d) c hc) (torusProjection u) =
      (((positiveFloor c (linearPartition (fun i => 4 * u i - 2)))⁻¹ : ℝ) : ℂ) := by
  have hsupport (y : d → ℝ) (hy : reciprocalCorrection c y ≠ 0) (i : d) : |y i| < 2 := by
    have hl := linearPartition_support (subset_closure (reciprocalCorrection_support c hc hy))
    have hh : |y i| ≤ 1 := abs_le.mpr ⟨hl.1 i, hl.2 i⟩
    linarith
  rw [assignmentReciprocalWiener, map_add, ContinuousMap.add_apply,
    toContinuous_real_smul, toContinuous_one, ContinuousMap.smul_apply, ContinuousMap.one_apply,
    compactChartWiener_value _ _ _ hsupport u hu]
  simp only [reciprocalCorrection, Complex.ofReal_sub, Complex.real_smul, mul_one]
  ring

end CausalLowerbound.PartC

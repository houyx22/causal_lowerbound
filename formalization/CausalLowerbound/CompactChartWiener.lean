import CausalLowerbound.PeriodizedWiener
import CausalLowerbound.WienerSpatialShift
import CausalLowerbound.MixedEvaluation

/-! Compact profiles in the physical carrier chart `v = 4u - 2`.
The representation is exact on the closed chart, including its boundary. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace CausalLowerbound.Wiener
variable {d : Type*} [Fintype d]

def compactChartWiener (f : (d → ℝ) → ℂ) (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f) :
    Fourier d :=
  spatialShift (torusProjection (fun _ => -(1 / 2)))
    (periodizedWiener f hf (hs.of_le (WithTop.coe_le_coe.mpr le_top)) (fun _ => 4) (by simp))

theorem compactChartWiener_value (f : (d → ℝ) → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (hsupport : ∀ y, f y ≠ 0 → ∀ i, |y i| < 2)
    (u : d → ℝ) (hu : u ∈ Set.Icc 0 1) :
    toContinuous (compactChartWiener f hf hs) (torusProjection u) = f (fun i => 4 * u i - 2) := by
  rw [compactChartWiener, spatialShift_value, periodizedWiener_value]
  have he : torusProjection u + torusProjection (fun _ => -(1 / 2)) =
      torusProjection (fun i => u i - 1 / 2) := by
    funext i
    simp only [torusProjection, Pi.add_apply, sub_eq_add_neg, QuotientAddGroup.mk_add]
  rw [he, periodizedTorus_coe, periodize_no_extra_copies_closed]
  · congr 1
    funext i
    norm_num
    ring
  · intro y hy i
    norm_num only [Nat.cast_ofNat, show (4 : ℝ) / 2 = 2 by norm_num]
    exact hsupport y hy i
  · intro i
    have h0 : 0 ≤ u i := hu.1 i
    have h1 : u i ≤ 1 := hu.2 i
    norm_num
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end CausalLowerbound.Wiener

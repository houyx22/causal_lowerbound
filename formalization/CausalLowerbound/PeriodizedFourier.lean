import CausalLowerbound.LatticeUnfolding
import CausalLowerbound.PeriodizedTorus
import CausalLowerbound.WienerDerivativeDecay

/-! Fourier coefficients of actual periodized compact profiles. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory UnitAddTorus
open scoped BigOperators FourierTransform

namespace CausalLowerbound.Wiener

attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {α : Type*} [Fintype α]

theorem torusProjection_measurePreserving :
    MeasurePreserving (torusProjection (α := α)) (volume.restrict unitCell)
      (volume : Measure (Torus α)) := by
  have hcircle : MeasurePreserving ((↑) : ℝ → UnitAddCircle)
      (volume.restrict (Set.Ioc 0 1)) AddCircle.haarAddCircle := by
    simpa only [zero_add, AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul] using
      (AddCircle.measurePreserving_mk (1 : ℝ) 0)
  have h := measurePreserving_pi (fun _ : α => volume.restrict (Set.Ioc (0 : ℝ) 1))
    (fun _ : α => AddCircle.haarAddCircle) (fun _ => hcircle)
  simpa only [torusProjection, unitCell, volume_pi, Measure.restrict_pi_pi] using h

theorem integral_torus_eq_unitCell (g : C(Torus α, ℂ)) :
    (∫ x : Torus α, g x) = ∫ x in unitCell, g (torusProjection x) := by
  have h := torusProjection_measurePreserving (α := α)
  calc
    _ = ∫ x, g x ∂Measure.map torusProjection (volume.restrict unitCell) := by rw [h.map_eq]
    _ = _ := integral_map h.measurable.aemeasurable g.continuous.aestronglyMeasurable

theorem torusProjection_integer_translate (k : α → ℤ) (x : α → ℝ) :
    torusProjection (latticeTranslate (fun _ => 1) k x) = torusProjection x := by
  funext i
  have hk : ((k i : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).mpr ⟨k i, by simp⟩
  simp only [torusProjection, latticeTranslate, Nat.cast_one, one_mul,
    QuotientAddGroup.mk_add, hk, add_zero]

theorem periodize_character_mul (f : (α → ℝ) → ℂ) (k : α → ℤ) (x : α → ℝ) :
    periodize (fun y => mFourier k (torusProjection y) * f y) (fun _ => 1) x =
      mFourier k (torusProjection x) * periodize f (fun _ => 1) x := by
  simp only [periodize, torusProjection_integer_translate, tsum_mul_left]

/-- This coefficient identity uses the actual torus Haar integral and the
actual locally finite periodization, not an assumed coefficient formula. -/
theorem periodized_unit_coefficient (f : (α → ℝ) → ℂ) (hf : HasCompactSupport f)
    (hc : Continuous f) (k : α → ℤ) :
    mFourierCoeff (periodizedContinuous f hf hc (fun _ => 1) (by simp)) k =
      ∫ x, mFourier (-k) (torusProjection x) * f x := by
  let F := periodizedContinuous f hf hc (fun _ => 1) (by simp)
  have hg : Continuous (fun x : α → ℝ => mFourier (-k) (torusProjection x) * f x) :=
    ((mFourier (-k)).continuous.comp torusProjection_quotient.continuous).mul hc
  calc
    _ = ∫ x in unitCell, mFourier (-k) (torusProjection x) * F (torusProjection x) := by
      exact integral_torus_eq_unitCell ((mFourier (-k)) * F)
    _ = ∫ x in unitCell, mFourier (-k) (torusProjection x) * periodize f (fun _ => 1) x := by
      apply setIntegral_congr_fun measurableSet_unitCell
      intro x _
      change mFourier (-k) (torusProjection x) * periodizedTorus f (fun _ => 1) (torusProjection x) = _
      rw [periodizedTorus_coe]
      simp
    _ = ∫ x in unitCell, periodize (fun y => mFourier (-k) (torusProjection y) * f y) (fun _ => 1) x := by
      simp only [periodize_character_mul]
    _ = _ := integral_unitCell_periodize _ hf.mul_left hg

end CausalLowerbound.Wiener

import CausalLowerbound.WienerSeries
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Wiener series on a finite dimensional torus

This realizes ℓ¹ Fourier coefficients as actual continuous torus functions.
Coefficient extraction recovers the original sequence; thus the coefficient
norm is a genuine function norm rather than a norm on a redundant coding.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory UnitAddTorus

namespace CausalLowerbound.Wiener

attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

abbrev Torus (d : Type*) := UnitAddTorus d
abbrev Fourier (d : Type*) := Series (d → ℤ) ℂ

def toContinuous : Fourier d →L[ℂ] C(Torus d, ℂ) :=
  synthesis mFourier 1 (fun _ => (mFourier_norm).le)

theorem toContinuous_bound (a : Fourier d) : ‖toContinuous a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using norm_synthesis (𝕜 := ℂ)
    (mFourier (d := d)) 1 (fun _ => mFourier_norm.le) a

theorem evaluate_bound (a : Fourier d) (x : Torus d) : ‖toContinuous a x‖ ≤ ‖a‖ :=
  ((toContinuous a).norm_coe_le_norm x).trans (toContinuous_bound a)

theorem toContinuous_hasSum (a : Fourier d) :
    HasSum (fun k => a k • mFourier k) (toContinuous a) :=
  synthesis_hasSum mFourier 1 (fun _ => mFourier_norm.le) a

theorem coefficient_bound (f : C(Torus d, ℂ)) (k : d → ℤ) :
    ‖mFourierCoeff f k‖ ≤ ‖f‖ := by
  have h : ∀ x : Torus d, ‖mFourier (-k) x • f x‖ ≤ ‖f‖ := by
    intro x
    rw [norm_smul]
    calc
      _ ≤ 1 * ‖f‖ := mul_le_mul
        ((mFourier (-k)).norm_coe_le_norm x |>.trans_eq mFourier_norm)
        (f.norm_coe_le_norm x) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  simpa only [mFourierCoeff, measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const (μ := (volume : Measure (Torus d)))
      (Filter.Eventually.of_forall h)

/-- Fourier coefficient extraction as a bounded linear map on continuous functions. -/
def coefficient (k : d → ℤ) : C(Torus d, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => mFourierCoeff f k
      map_add' := by
        intro f g
        simp only [mFourierCoeff, ContinuousMap.add_apply, smul_add]
        exact integral_add
          (((mFourier (-k)).continuous.smul f.continuous).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
          (((mFourier (-k)).continuous.smul g.continuous).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
      map_smul' := by
        intro c f
        simp only [mFourierCoeff, ContinuousMap.smul_apply]
        simp_rw [smul_comm (mFourier (-k) _) c]
        exact integral_smul c _ }
    1 (fun f => by simpa only [one_mul] using coefficient_bound f k)

@[simp]
theorem coefficient_apply (k : d → ℤ) (f : C(Torus d, ℂ)) :
    coefficient k f = mFourierCoeff f k := rfl

theorem coefficient_character (k n : d → ℤ) :
    coefficient k (mFourier n) = if k = n then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := d))) k n
  simpa only [mFourierLp, ContinuousMap.inner_toLp, coefficient_apply, mFourierCoeff,
    smul_eq_mul, mFourier_neg, mul_comm] using h

theorem coefficient_toContinuous (a : Fourier d) (k : d → ℤ) :
    coefficient k (toContinuous a) = a k := by
  classical
  change coefficient k (synthesis mFourier 1 (fun _ => mFourier_norm.le) a) = _
  rw [synthesis_apply, (coefficient k).map_tsum
    (summable_synthesis mFourier 1 (fun _ => mFourier_norm.le) a)]
  simp only [map_smul, coefficient_character, smul_eq_mul]
  rw [tsum_eq_single k]
  · simp
  · intro n hn; simp [Ne.symm hn]

theorem toContinuous_injective : Function.Injective (toContinuous (d := d)) := by
  intro a b h
  apply lp.ext
  funext k
  rw [← coefficient_toContinuous a k, ← coefficient_toContinuous b k, h]

/-- The ℓ¹ norm is exactly the usual Wiener norm of the realized function. -/
theorem norm_eq_fourier_tsum (a : Fourier d) :
    ‖a‖ = ∑' k, ‖mFourierCoeff (toContinuous a) k‖ := by
  simp_rw [← coefficient_apply, coefficient_toContinuous]
  exact norm_eq_tsum a

theorem integral_toContinuous (a : Fourier d) :
    (∫ x : Torus d, toContinuous a x) = a 0 := by
  rw [← coefficient_toContinuous a 0, coefficient_apply, mFourierCoeff]
  simp only [neg_zero, mFourier_zero, ContinuousMap.one_apply, one_smul]

end CausalLowerbound.Wiener

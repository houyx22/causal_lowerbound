import CausalLowerbound.WienerFourier
import Mathlib.Tactic.Ring

/-! # Concrete real trigonometric elements of the Wiener space -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ComplexConjugate
open UnitAddTorus

namespace CausalLowerbound.Wiener

variable {d : Type*} [Fintype d]

def characterSeries (k : d → ℤ) : Fourier d := lp.single 1 k 1

theorem characterSeries_norm (k : d → ℤ) : ‖characterSeries k‖ = 1 := by
  rw [characterSeries, lp.norm_single (by norm_num), norm_one]

@[simp]
theorem characterSeries_toContinuous (k : d → ℤ) :
    toContinuous (characterSeries k) = mFourier k := by
  exact (synthesis_single mFourier 1 (fun _ => mFourier_norm.le) k (1 : ℂ)).trans (one_smul _ _)

def cosineSeries (k : d → ℤ) : Fourier d :=
  (1 / 2 : ℂ) • (characterSeries k + characterSeries (-k))

def sineSeries (k : d → ℤ) : Fourier d :=
  (-Complex.I / 2) • (characterSeries k - characterSeries (-k))

theorem cosineSeries_norm (k : d → ℤ) : ‖cosineSeries k‖ ≤ 1 := by
  calc
    _ = ‖(1 / 2 : ℂ)‖ * ‖characterSeries k + characterSeries (-k)‖ := norm_smul _ _
    _ ≤ ‖(1 / 2 : ℂ)‖ * (‖characterSeries k‖ + ‖characterSeries (-k)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = 1 := by rw [characterSeries_norm, characterSeries_norm]; norm_num

theorem sineSeries_norm (k : d → ℤ) : ‖sineSeries k‖ ≤ 1 := by
  calc
    _ = ‖-Complex.I / 2‖ * ‖characterSeries k - characterSeries (-k)‖ := norm_smul _ _
    _ ≤ ‖-Complex.I / 2‖ * (‖characterSeries k‖ + ‖characterSeries (-k)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ = 1 := by rw [characterSeries_norm, characterSeries_norm]; norm_num

theorem cosineSeries_value (k : d → ℤ) (x : Torus d) :
    toContinuous (cosineSeries k) x = ((mFourier k x).re : ℂ) := by
  simp only [cosineSeries, map_smul, map_add, characterSeries_toContinuous,
    ContinuousMap.smul_apply, ContinuousMap.add_apply, smul_eq_mul, mFourier_neg]
  rw [Complex.re_eq_add_conj]
  ring

theorem sineSeries_value (k : d → ℤ) (x : Torus d) :
    toContinuous (sineSeries k) x = ((mFourier k x).im : ℂ) := by
  simp only [sineSeries, map_smul, map_sub, characterSeries_toContinuous,
    ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul, mFourier_neg]
  rw [Complex.sub_conj]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  calc
    _ = -(Complex.I * Complex.I) * ((mFourier k x).im : ℂ) := by ring
    _ = _ := by simp

def trigSeries (k : d → ℤ) (b : Bool) : Fourier d :=
  if b then sineSeries k else cosineSeries k

def trigMean (k : d → ℤ) (b : Bool) : ℝ := if k = 0 ∧ b = false then 1 else 0

theorem trigMean_bound (k : d → ℤ) (b : Bool) : |trigMean k b| ≤ 1 := by
  unfold trigMean; split_ifs <;> norm_num

theorem trigSeries_norm (k : d → ℤ) (b : Bool) : ‖trigSeries k b‖ ≤ 1 := by
  cases b
  · exact cosineSeries_norm k
  · exact sineSeries_norm k

theorem trigSeries_real (k : d → ℤ) (b : Bool) (x : Torus d) :
    (toContinuous (trigSeries k b) x).im = 0 := by
  cases b <;> simp [trigSeries, sineSeries_value, cosineSeries_value]

theorem trigSeries_zero_coefficient (k : d → ℤ) (b : Bool) :
    trigSeries k b (0 : d → ℤ) = (trigMean k b : ℂ) := by
  classical
  cases b <;> by_cases hk : k = 0 <;>
    norm_num [trigSeries, trigMean, sineSeries, cosineSeries, characterSeries,
      lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, lp.single_apply, hk, eq_comm]

def centeredTrig (k : d → ℤ) (b : Bool) : Fourier d :=
  trigSeries k b - (trigMean k b : ℂ) • characterSeries 0

theorem centeredTrig_norm (k : d → ℤ) (b : Bool) : ‖centeredTrig k b‖ ≤ 1 := by
  classical
  by_cases hk : k = 0
  · subst k
    cases b <;> norm_num [centeredTrig, trigSeries, trigMean, sineSeries, cosineSeries,
      smul_add, ← add_smul]
  · simpa [centeredTrig, trigMean, hk] using trigSeries_norm k b

theorem centeredTrig_zero_coefficient (k : d → ℤ) (b : Bool) :
    centeredTrig k b (0 : d → ℤ) = 0 := by
  simp [centeredTrig, lp.coeFn_sub, lp.coeFn_smul, trigSeries_zero_coefficient,
    characterSeries, lp.single_apply_self]

theorem centeredTrig_real (k : d → ℤ) (b : Bool) (x : Torus d) :
    (toContinuous (centeredTrig k b) x).im = 0 := by
  simp [centeredTrig, map_sub, map_smul, characterSeries_toContinuous, mFourier_zero,
    ContinuousMap.sub_apply, ContinuousMap.smul_apply, trigSeries_real]

end CausalLowerbound.Wiener

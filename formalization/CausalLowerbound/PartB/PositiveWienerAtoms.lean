import CausalLowerbound.PartB.PolarizationAlgebra
import CausalLowerbound.WienerTrigonometric

/-!
# A fixed countable dictionary of positive Wiener densities

The atoms are explicit averages of small real trigonometric perturbations of
the constant density. Their Wiener norm, integral, and pointwise positivity
are proved. The dictionary depends on the degree and θ, not on the tensor
being decomposed.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open UnitAddTorus MeasureTheory

namespace CausalLowerbound.PartB
open Wiener Polarization

attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace PositiveWiener

variable {d ι : Type*} [Fintype d] [Fintype ι] [DecidableEq ι]

def averageSeries (f : ι → Fourier d) (b : ι → Bool) : Fourier d :=
  if maskMass b = 0 then characterSeries 0
  else ((maskMass b)⁻¹ : ℂ) • ∑ i, (select b i : ℂ) • f i

theorem averageSeries_norm (f : ι → Fourier d) (b : ι → Bool) (M : ℝ)
    (hM : 1 ≤ M) (hf : ∀ i, ‖f i‖ ≤ M) : ‖averageSeries f b‖ ≤ M := by
  by_cases h : maskMass b = 0
  · simpa only [averageSeries, if_pos h, characterSeries_norm] using hM
  · have hmass := maskMass_nonneg b
    have hs : ‖∑ i, (select b i : ℂ) • f i‖ ≤ maskMass b * M := by
      calc
        _ ≤ ∑ i, ‖(select b i : ℂ) • f i‖ := norm_sum_le _ _
        _ ≤ ∑ i, select b i * M := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (select_nonneg b i)]
          exact mul_le_mul_of_nonneg_left (hf i) (select_nonneg b i)
        _ = _ := by rw [← Finset.sum_mul]; rfl
    rw [averageSeries, if_neg h, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hmass]
    calc
      _ ≤ (maskMass b)⁻¹ * (maskMass b * M) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hmass)
      _ = M := by rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]

omit [DecidableEq ι] in
theorem averageSeries_zero (f : ι → Fourier d) (b : ι → Bool)
    (hf : ∀ i, f i 0 = 1) : averageSeries f b 0 = 1 := by
  by_cases h : maskMass b = 0
  · simp [averageSeries, h, characterSeries, lp.single_apply_self]
  · simp only [averageSeries, if_neg h, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sum,
      Finset.sum_apply, hf, smul_eq_mul, mul_one]
    have hs : (∑ i, (select b i : ℂ)) = (maskMass b : ℂ) := by
      simp only [maskMass, Complex.ofReal_sum]
    rw [hs, inv_mul_cancel₀ (by exact_mod_cast h)]

omit [DecidableEq ι] in
theorem averageSeries_value (f : ι → Fourier d) (b : ι → Bool) (x : Torus d) :
    toContinuous (averageSeries f b) x =
      if maskMass b = 0 then 1 else ((maskMass b)⁻¹ : ℂ) *
        ∑ i, (select b i : ℂ) * toContinuous (f i) x := by
  unfold averageSeries
  split_ifs <;> simp [map_smul, map_sum, characterSeries_toContinuous, mFourier_zero,
    ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul]

def affineSeries (g : ι → Fourier d) (θ : ℝ) (b : ι → Bool) (i : ι) : Fourier d :=
  if b i then characterSeries 0 + (θ : ℂ) • g i else characterSeries 0

omit [Fintype ι] [DecidableEq ι] in
theorem affineSeries_norm (g : ι → Fourier d) (θ : ℝ) (hθ : 0 ≤ θ)
    (hg : ∀ i, ‖g i‖ ≤ 1) (b : ι → Bool) (i : ι) :
    ‖affineSeries g θ b i‖ ≤ 1 + θ := by
  unfold affineSeries
  split_ifs
  · calc
      _ ≤ ‖characterSeries (0 : d → ℤ)‖ + ‖(θ : ℂ) • g i‖ := norm_add_le _ _
      _ = 1 + θ * ‖g i‖ := by
        rw [characterSeries_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ]
      _ ≤ 1 + θ := by nlinarith [hg i]
  · rw [characterSeries_norm]; linarith

omit [Fintype ι] [DecidableEq ι] in
theorem affineSeries_zero (g : ι → Fourier d) (θ : ℝ) (hg : ∀ i, g i 0 = 0)
    (b : ι → Bool) (i : ι) : affineSeries g θ b i 0 = 1 := by
  unfold affineSeries
  split_ifs <;> simp [lp.coeFn_add, lp.coeFn_smul, hg, characterSeries, lp.single_apply_self]

omit [Fintype ι] [DecidableEq ι] in
theorem affineSeries_value (g : ι → Fourier d) (θ : ℝ) (b : ι → Bool) (i : ι)
    (hreal : ∀ i x, (toContinuous (g i) x).im = 0) (x : Torus d) :
    toContinuous (affineSeries g θ b i) x =
      (affineDensity (fun i x => (toContinuous (g i) x).re) θ b i x : ℂ) := by
  unfold affineSeries affineDensity
  split_ifs <;> apply Complex.ext <;>
    simp [map_add, map_smul, characterSeries_toContinuous, mFourier_zero,
      ContinuousMap.add_apply, ContinuousMap.smul_apply, Complex.ofReal_add,
      Complex.ofReal_mul, smul_eq_mul, Complex.mul_re, Complex.mul_im, hreal]

def atomSeries (g : ι → Fourier d) (θ : ℝ)
    (m : (ι → Bool) × (ι → Bool)) : Fourier d := averageSeries (affineSeries g θ m.1) m.2

theorem atomSeries_value (g : ι → Fourier d) (θ : ℝ)
    (hreal : ∀ i x, (toContinuous (g i) x).im = 0)
    (m : (ι → Bool) × (ι → Bool)) (x : Torus d) :
    toContinuous (atomSeries g θ m) x =
      (stencilAtom (fun i x => (toContinuous (g i) x).re) θ m x : ℂ) := by
  rw [atomSeries, averageSeries_value]
  simp_rw [affineSeries_value g θ m.1 _ hreal]
  unfold stencilAtom averageAtom
  split_ifs <;> simp only [Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_sum,
    Complex.ofReal_inv]

abbrev AtomIndex (d ι : Type*) :=
  (ι → (d → ℤ) × Bool) × ((ι → Bool) × (ι → Bool))

def dictionary (θ : ℝ) (m : AtomIndex d ι) : Fourier d :=
  atomSeries (fun i => centeredTrig (m.1 i).1 (m.1 i).2) θ m.2

omit [DecidableEq ι] in
theorem dictionary_countable : Countable (AtomIndex d ι) := inferInstance

theorem dictionary_norm (θ : ℝ) (hθ : 0 ≤ θ) (m : AtomIndex d ι) :
    ‖dictionary θ m‖ ≤ 1 + θ := by
  apply averageSeries_norm _ _ (1 + θ) (by linarith)
  exact affineSeries_norm _ θ hθ (fun i => centeredTrig_norm _ _) _

theorem dictionary_integral (θ : ℝ) (m : AtomIndex d ι) :
    (∫ x : Torus d, toContinuous (dictionary θ m) x) = 1 := by
  rw [integral_toContinuous]
  apply averageSeries_zero
  exact affineSeries_zero _ θ (fun i => centeredTrig_zero_coefficient _ _) _

theorem dictionary_real (θ : ℝ) (m : AtomIndex d ι) (x : Torus d) :
    (toContinuous (dictionary θ m) x).im = 0 := by
  rw [dictionary, atomSeries_value _ θ (fun i x => centeredTrig_real _ _ x)]
  simp

theorem dictionary_bounds (θ : ℝ) (hθ : 0 ≤ θ) (m : AtomIndex d ι) (x : Torus d) :
    1 - θ ≤ (toContinuous (dictionary θ m) x).re ∧
      (toContinuous (dictionary θ m) x).re ≤ 1 + θ := by
  rw [dictionary, atomSeries_value _ θ (fun i x => centeredTrig_real _ _ x), Complex.ofReal_re]
  apply stencilAtom_bounds _ θ hθ
  intro i y
  exact (Complex.abs_re_le_norm _).trans ((evaluate_bound _ y).trans (centeredTrig_norm _ _))

theorem dictionary_positive (θ : ℝ) (hθ : 0 ≤ θ) (hlt : θ < 1)
    (m : AtomIndex d ι) (x : Torus d) : 0 < (toContinuous (dictionary θ m) x).re := by
  have h := (dictionary_bounds θ hθ m x).1
  linarith

end PositiveWiener
end CausalLowerbound.PartB

import CausalLowerbound.PeriodizedFourier
import CausalLowerbound.FourierRescaling
import CausalLowerbound.WienerReconstruction

/-! Identification of the actual anisotropic periodization coefficients with
normalized Euclidean Fourier samples, followed by the Wiener estimate. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory UnitAddTorus
open scoped BigOperators FourierTransform ContDiff

namespace CausalLowerbound.Wiener

attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {α : Type*} [Fintype α]

theorem periodize_coordinateScale (f : (α → ℝ) → ℂ) (N : α → ℕ) (x : α → ℝ) :
    periodize (f ∘ coordinateScale N) (fun _ => 1) x =
      periodize f N (coordinateScale N x) := by
  unfold periodize
  apply tsum_congr
  intro k
  apply congrArg f
  funext i
  simp only [Function.comp_apply, coordinateScale, latticeTranslate, Nat.cast_one, one_mul]
  ring

theorem periodizedTorus_coordinateScale (f : (α → ℝ) → ℂ) (N : α → ℕ) (x : Torus α) :
    periodizedTorus (f ∘ coordinateScale N) (fun _ => 1) x = periodizedTorus f N x := by
  simp only [periodizedTorus, Nat.cast_one, one_mul, periodize_coordinateScale, coordinateScale]
  rfl

/-- Every actual coefficient is the normalized Fourier sample, with one
inverse period per coordinate. All normalization factors are explicit. -/
theorem periodized_coefficient_eq_sampled (f : (α → ℝ) → ℂ) (hf : HasCompactSupport f)
    (hc : Continuous f) (N : α → ℕ) (hN : ∀ i, N i ≠ 0) (k : α → ℤ) :
    mFourierCoeff (periodizedContinuous f hf hc N hN) k =
      sampledFourier (fun y : EuclideanSpace ℝ α => f (fun i => y i)) N k := by
  let g := f ∘ coordinateScale N
  have hg : HasCompactSupport g := hf.comp_homeomorph (scaleHomeomorph N hN)
  have hgc : Continuous g := hc.comp (scaleHomeomorph N hN).continuous
  have he : periodizedContinuous f hf hc N hN =
      periodizedContinuous g hg hgc (fun _ => 1) (by simp) := by
    apply ContinuousMap.ext
    intro x
    exact (periodizedTorus_coordinateScale f N x).symm
  rw [he, periodized_unit_coefficient g hg hgc]
  calc
    _ = ∫ x, fourierPhase (fun i => (k i : ℝ) / N i) (coordinateScale N x) *
        f (coordinateScale N x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [fourierPhase_scaled N hN k x, mFourier_projection_phase]
      rfl
    _ = (∏ i, (N i : ℝ)⁻¹) • ∫ y, fourierPhase (fun i => (k i : ℝ) / N i) y * f y :=
      integral_coordinateScale (fun y => fourierPhase (fun i => (k i : ℝ) / N i) y * f y) N hN
    _ = _ := by
      unfold sampledFourier
      congr 1
      exact (fourierIntegral_pi f (gridPoint N k)).symm

theorem periodized_wiener_bound (f : (α → ℝ) → ℂ) (hf : HasCompactSupport f)
    (hc : Continuous f)
    (hdiff : ContDiff ℝ ((2 * Fintype.card α : ℕ) : ℕ∞)
      (fun y : EuclideanSpace ℝ α => f (fun i => y i)))
    (hcompact : HasCompactSupport (fun y : EuclideanSpace ℝ α => f (fun i => y i)))
    (N : α → ℕ) (hN : ∀ i, N i ≠ 0) :
    Summable (fun k => ‖mFourierCoeff (periodizedContinuous f hf hc N hN) k‖) ∧
      (∑' k, ‖mFourierCoeff (periodizedContinuous f hf hc N hN) k‖) ≤
        derivativeDecayConstant (fun y : EuclideanSpace ℝ α => f (fun i => y i)) (Fintype.card α) *
          latticeConstant ^ Fintype.card α := by
  simp_rw [periodized_coefficient_eq_sampled]
  exact sampledFourier_wiener_bound _ hdiff (compact_derivatives_integrable _ _ hdiff hcompact) N hN

/-- An actual Wiener element for the rescaled periodization of a compact
smooth function; no Fourier reconstruction identity is an assumption. -/
def periodizedWiener (f : (α → ℝ) → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiff ℝ ((2 * Fintype.card α : ℕ) : ℕ∞) f)
    (N : α → ℕ) (hN : ∀ i, N i ≠ 0) : Fourier α :=
  ofContinuous (periodizedContinuous f hf hs.continuous N hN)
    (periodized_wiener_bound f hf hs.continuous
      (hs.comp (EuclideanSpace.equiv α ℝ).contDiff)
      (hf.comp_homeomorph (EuclideanSpace.equiv α ℝ).toHomeomorph) N hN).1

theorem periodizedWiener_value (f : (α → ℝ) → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiff ℝ ((2 * Fintype.card α : ℕ) : ℕ∞) f)
    (N : α → ℕ) (hN : ∀ i, N i ≠ 0) (x : Torus α) :
    toContinuous (periodizedWiener f hf hs N hN) x = periodizedTorus f N x := by
  rw [periodizedWiener, toContinuous_ofContinuous]
  rfl

theorem periodizedWiener_bound (f : (α → ℝ) → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiff ℝ ((2 * Fintype.card α : ℕ) : ℕ∞) f)
    (N : α → ℕ) (hN : ∀ i, N i ≠ 0) :
    ‖periodizedWiener f hf hs N hN‖ ≤
      derivativeDecayConstant (fun y : EuclideanSpace ℝ α => f (fun i => y i))
        (Fintype.card α) * latticeConstant ^ Fintype.card α := by
  rw [periodizedWiener, norm_ofContinuous]
  exact (periodized_wiener_bound f hf hs.continuous
    (hs.comp (EuclideanSpace.equiv α ℝ).contDiff)
    (hf.comp_homeomorph (EuclideanSpace.equiv α ℝ).toHomeomorph) N hN).2

end CausalLowerbound.Wiener

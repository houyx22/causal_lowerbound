import CausalLowerbound.WienerFourier

/-! Reconstruct an actual Wiener element from a continuous function with
absolutely summable Fourier coefficients. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory UnitAddTorus

namespace CausalLowerbound.Wiener

attribute [local instance] Real.fact_zero_lt_one
local instance reconstructionMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance reconstructionHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance reconstructionProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {α : Type*} [Fintype α]

def ofContinuous (f : C(Torus α, ℂ))
    (hf : Summable (fun k => ‖mFourierCoeff f k‖)) : Fourier α :=
  ⟨mFourierCoeff f, memℓp_gen (by simpa using hf)⟩

@[simp]
theorem ofContinuous_apply (f : C(Torus α, ℂ))
    (hf : Summable (fun k => ‖mFourierCoeff f k‖)) (k : α → ℤ) :
    ofContinuous f hf k = mFourierCoeff f k := rfl

@[simp]
theorem toContinuous_ofContinuous (f : C(Torus α, ℂ))
    (hf : Summable (fun k => ‖mFourierCoeff f k‖)) :
    toContinuous (ofContinuous f hf) = f :=
  (toContinuous_hasSum (ofContinuous f hf)).unique
    (hasSum_mFourier_series_of_summable hf.of_norm)

theorem norm_ofContinuous (f : C(Torus α, ℂ))
    (hf : Summable (fun k => ‖mFourierCoeff f k‖)) :
    ‖ofContinuous f hf‖ = ∑' k, ‖mFourierCoeff f k‖ :=
  norm_eq_tsum (ofContinuous f hf)

end CausalLowerbound.Wiener

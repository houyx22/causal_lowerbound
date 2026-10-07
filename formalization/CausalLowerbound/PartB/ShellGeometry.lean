import CausalLowerbound.SmoothCompact
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Smooth rescaled profiles for the paper's explicit trigonometric embedding.
The scale zero is included, so compactness controls every fine dyadic scale. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff Topology BigOperators
open Filter

namespace CausalLowerbound.PartB.ShellGeometry

theorem analyticAt_complex_sin (x : ℂ) : AnalyticAt ℂ Complex.sin x := by
  unfold Complex.sin
  exact (((analyticAt_id.neg.mul analyticAt_const).cexp.sub
    (analyticAt_id.mul analyticAt_const).cexp).mul analyticAt_const).div
      analyticAt_const (by norm_num)

theorem analyticAt_real_sin (x : ℝ) : AnalyticAt ℝ Real.sin x := by
  have h : AnalyticAt ℝ (fun y : ℝ => (Complex.sin (y : ℂ)).re) x :=
    (Complex.reCLM.analyticAt _).comp
      ((analyticAt_complex_sin (x : ℂ)).restrictScalars.comp (Complex.ofRealCLM.analyticAt x))
  simpa using h

def sinc (x : ℝ) : ℝ := dslope Real.sin 0 x

@[simp] theorem sinc_zero : sinc 0 = 1 := by simp [sinc, Real.deriv_sin]

theorem sinc_of_ne {x : ℝ} (hx : x ≠ 0) : sinc x = Real.sin x / x := by
  simp [sinc, dslope_of_ne _ hx, slope, div_eq_mul_inv, mul_comm]

theorem mul_sinc (x : ℝ) : x * sinc x = Real.sin x := by
  simpa [sinc] using sub_smul_dslope Real.sin 0 x

theorem contDiff_sinc : ContDiff ℝ ∞ sinc := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    obtain ⟨p, hp⟩ := analyticAt_real_sin 0
    exact (show AnalyticAt ℝ sinc 0 from ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩).contDiffAt
  · have h : ContDiffAt ℝ ∞ (fun y : ℝ => Real.sin y / y) x :=
      Real.contDiff_sin.contDiffAt.div contDiffAt_id hx
    apply h.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    exact sinc_of_ne hy

theorem sinc_ne_zero {x : ℝ} (hx : |x| < Real.pi) : sinc x ≠ 0 := by
  by_cases h0 : x = 0
  · simp [h0]
  · rw [sinc_of_ne h0]
    apply div_ne_zero _ h0
    intro h
    exact h0 ((Real.sin_eq_zero_iff_of_lt_of_lt (abs_lt.mp hx).1 (abs_lt.mp hx).2).mp h)

variable {d : Type*} [Fintype d]

/-- Coordinates are indexed by `(coordinate, sine?)`. -/
def embedding (u : d → ℝ) (a : d × Bool) : ℝ :=
  if a.2 then Real.sin (2 * Real.pi * u a.1) else Real.cos (2 * Real.pi * u a.1)

def radial (τ : ℝ) (z : d → ℝ) (i : d) : ℝ :=
  2 * Real.pi * z i * sinc (Real.pi * τ * z i)

def chordSquare (τ : ℝ) (z : d → ℝ) : ℝ := ∑ i, (radial τ z i) ^ 2

def chordProfile (τ : ℝ) (z : d → ℝ) : ℝ := Real.sqrt (chordSquare τ z)

def differenceProfile (τ : ℝ) (u z : d → ℝ) (a : d × Bool) : ℝ :=
  radial τ z a.1 *
    (if a.2 then Real.cos (2 * Real.pi * u a.1 + Real.pi * τ * z a.1)
      else -Real.sin (2 * Real.pi * u a.1 + Real.pi * τ * z a.1))

def coefficientProfile (τ : ℝ) (u z : d → ℝ) (a : d × Bool) : ℝ :=
  differenceProfile τ u z a / chordSquare τ z

def constantProfile (τ : ℝ) (u z : d → ℝ) : ℝ :=
  (∑ a, embedding u a * differenceProfile τ u z a) / chordSquare τ z

theorem radial_mul_scale (τ : ℝ) (z : d → ℝ) (i : d) :
    τ * radial τ z i = 2 * Real.sin (Real.pi * τ * z i) := by
  have h := mul_sinc (Real.pi * τ * z i)
  dsimp [radial]
  nlinarith

theorem differenceProfile_mul_scale (τ : ℝ) (u z : d → ℝ) (a : d × Bool) :
    τ * differenceProfile τ u z a = embedding (fun i => u i + τ * z i) a - embedding u a := by
  rw [differenceProfile, ← mul_assoc, radial_mul_scale]
  rcases a with ⟨i, b⟩
  cases b <;> simp only [embedding, Bool.false_eq_true, ↓reduceIte]
  · rw [Real.cos_sub_cos]
    have hs : (2 * Real.pi * (u i + τ * z i) + 2 * Real.pi * u i) / 2 =
        2 * Real.pi * u i + Real.pi * τ * z i := by ring
    have hd : (2 * Real.pi * (u i + τ * z i) - 2 * Real.pi * u i) / 2 =
        Real.pi * τ * z i := by ring
    rw [hs, hd]
    ring
  · rw [Real.sin_sub_sin]
    congr 1 <;> congr 1 <;> ring

end CausalLowerbound.PartB.ShellGeometry

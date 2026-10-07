import CausalLowerbound.PartB.IdealIncrementLogBound
import CausalLowerbound.PartB.LogarithmicScale

/-! The actual ideal increment as a Wiener element, and its vanishing norm
at the polynomial/logarithmic scales used in Part B. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology BigOperators

namespace CausalLowerbound.PartB.ShellGeometry
open Wiener

variable {Ω K V E d : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype d] [DecidableEq d]

theorem fourier_ext_real {A B : Fourier (V × d)}
    (h : ∀ u, toContinuous A (torusProjection u) = toContinuous B (torusProjection u)) : A = B := by
  apply toContinuous_injective
  ext x
  simpa using h (torusRepresentative x)

def idealWiener (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (amp t : ℝ) (hamp : 0 ≤ amp) (ht : 0 < t) : Fourier (V × d) :=
  Classical.choose ((ideal_increment_wiener_bound a b μ U ν).choose_spec.2 amp hamp t ht)

theorem idealWiener_value (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (amp t : ℝ) (hamp : 0 ≤ amp) (ht : 0 < t) (u : V × d → ℝ) :
    toContinuous (idealWiener a b μ U ν amp t hamp ht) (torusProjection u) =
      (idealIncrement a b μ U ν amp t u : ℝ) :=
  (Classical.choose_spec ((ideal_increment_wiener_bound a b μ U ν).choose_spec.2 amp hamp t ht)).1 u

theorem idealWiener_log_bound (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) :
    ∃ C ≥ 0, ∀ amp (hamp : 0 ≤ amp) t (ht : 0 < t), t ≤ 1 →
      ‖idealWiener a b μ U ν amp t hamp ht‖ ≤
        C * (1 + Real.log (1 / t)) ^ Fintype.card E *
          ∑ j ∈ Finset.Icc 2 (Fintype.card K), (amp / t) ^ j := by
  obtain ⟨C, hC, hb⟩ := ideal_increment_log_wiener_bound a b μ U ν
  refine ⟨C, hC, ?_⟩
  intro amp hamp t ht ht1
  obtain ⟨A, hA, hn⟩ := hb amp hamp t ⟨ht, ht1⟩
  have he : idealWiener a b μ U ν amp t hamp ht = A :=
    fourier_ext_real (fun u => (idealWiener_value a b μ U ν amp t hamp ht u).trans (hA u).symm)
  rwa [he]

/-- Taking x=n+1 only avoids the irrelevant n=0 endpoint. -/
def idealWienerSequence (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (p B : ℝ) (n : ℕ) : Fourier (V × d) :=
  idealWiener a b μ U ν (polynomialAmplitude p (n + 1)) (logarithmicThreshold p B (n + 1))
    (polynomialAmplitude_pos p (by positivity)).le
    (logarithmicThreshold_pos p B (le_add_of_nonneg_left (Nat.cast_nonneg n)))

theorem idealWienerSequence_rate (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (p B : ℝ) (hp : 0 < p) (hB : 0 ≤ B) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖idealWienerSequence a b μ U ν p B n‖ ≤
        C * logScale (n + 1) ^ ((Fintype.card E : ℝ) - 2 * B) := by
  obtain ⟨C, hC, hb⟩ := idealWiener_log_bound a b μ U ν
  refine ⟨C * ((1 + p) ^ Fintype.card E * (Fintype.card K + 1)), by positivity, ?_⟩
  have hx : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have ht := ((logarithmicThreshold_tendsto p B hp hB).comp hx).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [ht] with n hn
  apply (hb _ _ _ _ hn.le).trans
  have hm := mul_le_mul_of_nonneg_left
    (logarithmic_majorant_bound (Fintype.card E) (Fintype.card K) p B hp.le hB
      (le_add_of_nonneg_left (Nat.cast_nonneg n)) hn.le) hC
  simpa only [mul_assoc] using hm

theorem idealWienerSequence_norm_tendsto (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (p B : ℝ) (hp : 0 < p) (hB : (Fintype.card E : ℝ) < 2 * B) :
    Tendsto (fun n => ‖idealWienerSequence a b μ U ν p B n‖) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := by have := Nat.cast_nonneg (α := ℝ) (Fintype.card E); linarith
  obtain ⟨C, hC, hb⟩ := idealWienerSequence_rate a b μ U ν p B hp hB0
  have hx : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have hlim := ((logarithmic_majorant_tendsto (Fintype.card E) B hB).comp hx).const_mul C
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hb
  simpa using hlim

end CausalLowerbound.PartB.ShellGeometry

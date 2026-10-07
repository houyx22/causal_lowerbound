import CausalLowerbound.PartC.CarrierCoefficientWiener
import CausalLowerbound.PartC.NormalizedPropensityCorrection

/-! The normalized correction now uses the actual coarse envelope and
the actual assignment multiplier. Its value is exact even where the
assignment multiplier vanishes, and its norm is uniform in the block. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC

open Wiener PartB PartB.ShellGeometry
attribute [local instance] Real.fact_zero_lt_one
variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]

theorem fourier_real_of_closed_chart (A : Fourier d)
    (hA : ∀ u ∈ Set.Icc (0 : d → ℝ) 1, (toContinuous A (torusProjection u)).im = 0)
    (x : Torus d) : (toContinuous A x).im = 0 := by
  let u : d → ℝ := fun i => (AddCircle.equivIco (1 : ℝ) 0 (x i)).val
  have hu : u ∈ Set.Icc 0 1 := by
    constructor
    · intro i
      exact (AddCircle.equivIco (1 : ℝ) 0 (x i)).property.1
    · intro i
      simpa only [zero_add] using (AddCircle.equivIco (1 : ℝ) 0 (x i)).property.2.le
  have he : torusProjection u = x := by
    funext i
    exact (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (x i)
  rw [← he]
  exact hA u hu

theorem exists_physicalPropensityCorrection :
    ∃ C ≥ 0, ∀ (x₀ : d → ℝ) (r h : ℝ), 0 < r → r ≤ h →
      ∀ (k : activeBlocks (d := d) r h) (c w N ja : ℝ), 0 < w → w ≤ 1 / 2 → 0 < N →
      ∀ M : Fourier d, ‖M‖ ≤ N →
      (∀ u ∈ Set.Icc (0 : d → ℝ) 1, toContinuous M (torusProjection u) =
        (assignmentMultiplier c w (fun j => 4 * u j - 2) : ℂ)) → C * ja ^ 2 ≤ 1 →
      ∃ κ : V → Fourier (V × d), (∀ i, ‖κ i‖ ≤ 1) ∧
        (∀ i x, (toContinuous (κ i) x).im = 0) ∧
        ∀ i u, u ∈ Set.Icc (0 : V × d → ℝ) 1 →
          toContinuous (κ i) (torusProjection u) =
            ((assignmentMultiplier c w (fun j => 4 * u (i, j) - 2) / N) ^ 2 *
              ja ^ 2 * coarseBump x₀ h (fun j => x₀ j + r * (k.val j + 4 * u (i, j) - 2)) ^ 4 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_carrier_coarsePower_wiener (d := d) 4
  refine ⟨C, hC, fun x₀ r h hr hrh k c w N ja hw hw1 hN M hM hMv hsmall => ?_⟩
  obtain ⟨F, hF, hFr, hFv⟩ := hb x₀ r h hr hrh k
  let K : Fourier d := (ja ^ 2 : ℝ) • F
  have hK : ‖K‖ ≤ 1 := by
    calc
      ‖K‖ = ja ^ 2 * ‖F‖ := by simp only [K, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ja)]
      _ ≤ ja ^ 2 * C := mul_le_mul_of_nonneg_left hF (sq_nonneg ja)
      _ ≤ 1 := by simpa only [mul_comm] using hsmall
  have hKr (x : Torus d) : (toContinuous K x).im = 0 := by
    simp only [K, toContinuous_real_smul, ContinuousMap.smul_apply, Complex.real_smul,
      Complex.mul_im, Complex.ofReal_im, zero_mul, Complex.ofReal_re, hFr, mul_zero, add_zero]
  have hMr (x : Torus d) : (toContinuous M x).im = 0 :=
    fourier_real_of_closed_chart M (fun u hu => by rw [hMv u hu]; rfl) x
  let κ : V → Fourier (V × d) := normalizedPropensityCorrection M K N
  refine ⟨κ, normalizedPropensityCorrection_bound M K N hN hM hK, ?_, ?_⟩
  · intro i x
    have heM : toContinuous M (fun j => x (i, j)) = ((toContinuous M (fun j => x (i, j))).re : ℂ) :=
      Complex.ext rfl (by simpa only [Complex.ofReal_im] using hMr (fun j => x (i, j)))
    have heK : toContinuous K (fun j => x (i, j)) = ((toContinuous K (fun j => x (i, j))).re : ℂ) :=
      Complex.ext rfl (by simpa only [Complex.ofReal_im] using hKr (fun j => x (i, j)))
    rw [show κ i = normalizedPropensityCorrection M K N i from rfl,
      normalizedPropensityCorrection_value M K N i x _ _ heM heK]
    rfl
  · intro i u hu
    have hui : (fun j => u (i, j)) ∈ Set.Icc (0 : d → ℝ) 1 :=
      ⟨fun j => hu.1 (i, j), fun j => hu.2 (i, j)⟩
    have heK : toContinuous K (torusProjection (fun j => u (i, j))) =
        (ja ^ 2 * (carrierCoefficientCutoff (fun j => 4 * u (i, j) - 2) *
          coarseBump x₀ h (fun j => x₀ j + r * (k.val j + 4 * u (i, j) - 2)) ^ 4) : ℝ) := by
      simp only [K, toContinuous_real_smul, ContinuousMap.smul_apply, hFv _ hui,
        Complex.real_smul, Complex.ofReal_mul]
    rw [show κ i = normalizedPropensityCorrection M K N i from rfl,
      normalizedPropensityCorrection_value M K N i (torusProjection u) _ _ (hMv _ hui) heK]
    by_cases hm : assignmentMultiplier c w (fun j => 4 * u (i, j) - 2) = 0
    · simp only [hm, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, Complex.ofReal_zero]
    · rw [carrierCoefficientCutoff_on_assignment c w hw hw1 _ hm]
      congr 1
      ring

end CausalLowerbound.PartC

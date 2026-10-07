import CausalLowerbound.PartC.PhysicalPropensityCorrection
import CausalLowerbound.PartC.NormalizedRoughMoments

/-! Fourier representatives of the actual normalized rough variance.
The bound is a fixed constant: no smallness condition on the smooth
amplitude, fine scale, or number of rough signs is needed. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC
open Wiener PartB PartB.ShellGeometry
variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]

theorem normalizedPropensityCorrection_norm_bound (M K : Fourier d) (N L : ℝ)
    (hN : 0 < N) (hM : ‖M‖ ≤ N) (hK : ‖K‖ ≤ L) (i : V) :
    ‖normalizedPropensityCorrection M K N i‖ ≤ L := by
  have hnorm : ‖(N⁻¹ : ℝ) • M‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hN)]
    exact (mul_le_mul_of_nonneg_left hM (inv_nonneg.mpr hN.le)).trans_eq (inv_mul_cancel₀ hN.ne')
  apply (liftSlot_norm _ _).trans
  apply (norm_mul_le _ _).trans
  calc
    ‖((N⁻¹ : ℝ) • M) ^ 2‖ * ‖K‖ ≤ 1 * L :=
      mul_le_mul ((norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) hnorm)) hK
        (norm_nonneg _) (by norm_num)
    _ = L := one_mul _

theorem exists_physicalOutcomeVariance :
    ∃ L ≥ 1, ∀ (x₀ : d → ℝ) (r h : ℝ), 0 < r → r ≤ h →
      ∀ (k : activeBlocks (d := d) r h) (c w N : ℝ), 0 < w → w ≤ 1 / 2 → 0 < N →
      ∀ M : Fourier d, ‖M‖ ≤ N →
      (∀ u ∈ Set.Icc (0 : d → ℝ) 1, toContinuous M (torusProjection u) =
        (assignmentMultiplier c w (fun j => 4 * u j - 2) : ℂ)) →
      ∃ κ : V → Fourier (V × d), (∀ i, ‖κ i‖ ≤ L) ∧
        (∀ i x, (toContinuous (κ i) x).im = 0) ∧
        ∀ i u, u ∈ Set.Icc (0 : V × d → ℝ) 1 →
          toContinuous (κ i) (torusProjection u) =
            (normalizedRoughVariance x₀ r h k.val c w N (fun j => u (i, j)) : ℂ) := by
  obtain ⟨C, hC, hb⟩ := exists_carrier_coarsePower_wiener (d := d) 2
  refine ⟨1 + C, by linarith, fun x₀ r h hr hrh k c w N hw hw1 hN M hM hMv => ?_⟩
  obtain ⟨F, hF, hFr, hFv⟩ := hb x₀ r h hr hrh k
  have hMr (x : Torus d) : (toContinuous M x).im = 0 :=
    fourier_real_of_closed_chart M (fun u hu => by rw [hMv u hu]; rfl) x
  let κ : V → Fourier (V × d) := normalizedPropensityCorrection M F N
  refine ⟨κ, fun i => normalizedPropensityCorrection_norm_bound M F N (1 + C) hN hM
    (hF.trans (by linarith)) i, ?_, ?_⟩
  · intro i x
    have heM : toContinuous M (fun j => x (i, j)) = ((toContinuous M (fun j => x (i, j))).re : ℂ) :=
      Complex.ext rfl (by simpa only [Complex.ofReal_im] using hMr (fun j => x (i, j)))
    have heF : toContinuous F (fun j => x (i, j)) = ((toContinuous F (fun j => x (i, j))).re : ℂ) :=
      Complex.ext rfl (by simpa only [Complex.ofReal_im] using hFr (fun j => x (i, j)))
    rw [show κ i = normalizedPropensityCorrection M F N i from rfl,
      normalizedPropensityCorrection_value M F N i x _ _ heM heF]
    rfl
  · intro i u hu
    have hui : (fun j => u (i, j)) ∈ Set.Icc (0 : d → ℝ) 1 :=
      ⟨fun j => hu.1 (i, j), fun j => hu.2 (i, j)⟩
    rw [show κ i = normalizedPropensityCorrection M F N i from rfl,
      normalizedPropensityCorrection_value M F N i (torusProjection u) _ _ (hMv _ hui) (hFv _ hui)]
    unfold normalizedRoughVariance roughChartPoint
    by_cases hm : assignmentMultiplier c w (fun j => 4 * u (i, j) - 2) = 0
    · simp only [hm, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    · rw [carrierCoefficientCutoff_on_assignment c w hw hw1 _ hm, one_mul]

end CausalLowerbound.PartC

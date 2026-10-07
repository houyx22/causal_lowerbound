import CausalLowerbound.PartC.PhysicalRepresentativeEvaluation

/-! Changing one shared sign affects a normalized rough chart only on
the corresponding fine packet. Its integrated effect is O((ell/r)^d/N),
including packets meeting the boundary of the carrier chart. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem physicalRoughField_one_sign_sub_bound (x₀ : d → ℝ) (ℓ h : ℝ)
    (j : activeBlocks (d := d) ℓ h) (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (he : ∀ i, i ≠ j → ζ i = ζ' i) (x : d → ℝ) :
    |physicalRoughField x₀ ℓ h ζ x - physicalRoughField x₀ ℓ h ζ' x| ≤
      2 * |packet (coarseBump x₀ h) x₀ ℓ j.val x| := by
  rw [physicalRoughField_eq_sum, physicalRoughField_eq_sum, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single j]
  · rw [← mul_sub, abs_mul]
    have hs : |sign (ζ j) - sign (ζ' j)| ≤ 2 := by
      cases ζ j <;> cases ζ' j <;> norm_num [sign]
    exact (mul_le_mul_of_nonneg_left hs (abs_nonneg _)).trans_eq (mul_comm _ _)
  · intro i _ hij
    rw [he i hij, sub_self]
  · simp

theorem normalizedRoughChart_one_sign_sub_bound (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (hc : 0 < c) (hN : 0 < N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (j : activeBlocks (d := d) ℓ h) (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (he : ∀ i, i ≠ j → ζ i = ζ' i) (u : d → ℝ) :
    |normalizedRoughChart x₀ ℓ r h k c w N ζ u - normalizedRoughChart x₀ ℓ r h k c w N ζ' u| ≤
      (2 / (c * N)) * |roughPacketChart x₀ ℓ r h k j.val u| := by
  rw [normalizedRoughChart, normalizedRoughChart, ← sub_div, ← mul_sub,
    abs_div, abs_mul, abs_of_pos hN, abs_of_nonneg (hm _).1]
  calc
    _ ≤ ((1 / c) * (2 * |roughPacketChart x₀ ℓ r h k j.val u|)) / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      exact mul_le_mul (hm _).2
        (physicalRoughField_one_sign_sub_bound x₀ ℓ h j ζ ζ' he (roughChartPoint x₀ r k u))
        (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem normalizedRoughChart_one_sign_lintegral (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (c w N : ℝ) (hc : 0 < c) (hN : 0 < N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (j : activeBlocks (d := d) ℓ h) (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (he : ∀ i, i ≠ j → ζ i = ζ' i) :
    (∫⁻ u, ENNReal.ofReal |normalizedRoughChart x₀ ℓ r h k c w N ζ u -
      normalizedRoughChart x₀ ℓ r h k c w N ζ' u| ∂cubeMeasure d) ≤
        ENNReal.ofReal ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d) := by
  have hC : 0 ≤ 2 / (c * N) := by positivity
  have hp : (∫⁻ u, ENNReal.ofReal |roughPacketChart x₀ ℓ r h k j.val u| ∂cubeMeasure d) ≤
      ENNReal.ofReal (ℓ / (2 * r)) ^ Fintype.card d :=
    (setLIntegral_le_lintegral _ _).trans (roughPacketChart_lintegral x₀ ℓ r h k j.val hℓ hr)
  calc
    _ ≤ ∫⁻ u, ENNReal.ofReal ((2 / (c * N)) * |roughPacketChart x₀ ℓ r h k j.val u|) ∂cubeMeasure d :=
      lintegral_mono (fun u => ENNReal.ofReal_le_ofReal
        (normalizedRoughChart_one_sign_sub_bound x₀ ℓ r h k c w N hc hN hm j ζ ζ' he u))
    _ = ENNReal.ofReal (2 / (c * N)) *
        ∫⁻ u, ENNReal.ofReal |roughPacketChart x₀ ℓ r h k j.val u| ∂cubeMeasure d := by
      simp only [ENNReal.ofReal_mul hC]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 / (c * N)) * ENNReal.ofReal (ℓ / (2 * r)) ^ Fintype.card d :=
      mul_le_mul_left' hp _
    _ = _ := by rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ℓ / (2 * r)),
      ← ENNReal.ofReal_mul hC]

theorem normalizedRoughChart_one_sign_integral (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (c w N : ℝ) (hc : 0 < c) (hN : 0 < N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (j : activeBlocks (d := d) ℓ h) (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (he : ∀ i, i ≠ j → ζ i = ζ' i) :
    (∫ u, |normalizedRoughChart x₀ ℓ r h k c w N ζ u -
      normalizedRoughChart x₀ ℓ r h k c w N ζ' u| ∂cubeMeasure d) ≤
        (2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d := by
  have hn := norm_integral_le_lintegral_norm (μ := cubeMeasure d)
    (fun u => |normalizedRoughChart x₀ ℓ r h k c w N ζ u - normalizedRoughChart x₀ ℓ r h k c w N ζ' u|)
  simp only [Real.norm_eq_abs, abs_abs] at hn
  exact (le_abs_self _).trans (hn.trans ((ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (normalizedRoughChart_one_sign_lintegral x₀ ℓ r h k hℓ hr c w N hc hN hm j ζ ζ' he)).trans_eq
      (ENNReal.toReal_ofReal (by positivity))))

end CausalLowerbound.PartC

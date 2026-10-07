import CausalLowerbound.PartC.PositiveRepresentativeFactors
import CausalLowerbound.PartC.NormalizedTrigCentering

/-! Actual centered and positive one-slot density atoms on the closed unit
chart. The centering is the physical integral, not a prescribed moment. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry Representative

variable {d : Type*} [Fintype d] [DecidableEq d] {D : ℕ}

def physicalCenteredFactor (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (e : Fin (D + 1)) (q : d → ℤ) (b : Bool) : Factor d (activeBlocks (d := d) ℓ h) D :=
  centeredFactor e q b (normalizedTrigCenter x₀ ℓ r h k c w N e.val q b)

theorem physicalCenteredFactor_value (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (e : Fin (D + 1)) (q : d → ℤ) (b : Bool)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) :
    (factorValue (Wiener.torusProjection u) (normalizedRoughChart x₀ ℓ r h k c w N ζ u) ζ
      (physicalCenteredFactor x₀ ℓ r h k c w N e q b)).re =
      (1 / 2) * (normalizedRoughChart x₀ ℓ r h k c w N ζ u ^ e.val *
        (Wiener.toContinuous (Wiener.trigSeries q b) (Wiener.torusProjection u)).re -
          Walsh.evaluate ζ (normalizedTrigCenter x₀ ℓ r h k c w N e.val q b)) := by
  rw [physicalCenteredFactor, centeredFactor_value]
  simp only [Complex.real_smul, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

theorem physicalCenteredFactor_continuous (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (hc : 0 < c) (e : Fin (D + 1)) (q : d → ℤ) (b : Bool)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    Continuous (fun u => (factorValue (Wiener.torusProjection u)
      (normalizedRoughChart x₀ ℓ r h k c w N ζ u) ζ (physicalCenteredFactor x₀ ℓ r h k c w N e q b)).re) := by
  simp_rw [physicalCenteredFactor_value]
  have hg := ((normalizedRoughChart_continuous x₀ ℓ r h k c w N hc ζ).pow e.val).mul
    (Complex.continuous_re.comp ((Wiener.toContinuous (Wiener.trigSeries q b)).continuous.comp
      Wiener.torusProjection_quotient.continuous))
  exact continuous_const.mul (hg.sub continuous_const)

theorem physicalCenteredFactor_integral (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (hc : 0 < c) (e : Fin (D + 1)) (q : d → ℤ) (b : Bool)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    (∫ u in Set.Icc (0 : d → ℝ) 1, (factorValue (Wiener.torusProjection u)
      (normalizedRoughChart x₀ ℓ r h k c w N ζ u) ζ (physicalCenteredFactor x₀ ℓ r h k c w N e q b)).re) = 0 := by
  let g := fun u => normalizedRoughChart x₀ ℓ r h k c w N ζ u ^ e.val *
    (Wiener.toContinuous (Wiener.trigSeries q b) (Wiener.torusProjection u)).re
  have hg : Continuous g :=
    ((normalizedRoughChart_continuous x₀ ℓ r h k c w N hc ζ).pow e.val).mul
      (Complex.continuous_re.comp ((Wiener.toContinuous (Wiener.trigSeries q b)).continuous.comp
        Wiener.torusProjection_quotient.continuous))
  have hi : IntegrableOn g (Set.Icc (0 : d → ℝ) 1) :=
    hg.continuousOn.integrableOn_compact isCompact_Icc
  have hvol : volume (Set.Icc (0 : d → ℝ) 1) = 1 := by simp [Real.volume_Icc_pi]
  have hconst : IntegrableOn (fun _ : d → ℝ =>
      Walsh.evaluate ζ (normalizedTrigCenter x₀ ℓ r h k c w N e.val q b)) (Set.Icc 0 1) :=
    integrableOn_const.mpr (Or.inr (by simp [hvol]))
  have hm := normalizedTrigCenter_evaluate x₀ ℓ r h k c w N hc e.val q b ζ
  change Walsh.evaluate ζ (normalizedTrigCenter x₀ ℓ r h k c w N e.val q b) =
    ∫ u in Set.Icc (0 : d → ℝ) 1, g u at hm
  simp_rw [physicalCenteredFactor_value]
  change (∫ u in Set.Icc (0 : d → ℝ) 1, (1 / 2) *
    (g u - Walsh.evaluate ζ (normalizedTrigCenter x₀ ℓ r h k c w N e.val q b))) = 0
  rw [integral_const_mul, integral_sub hi hconst, setIntegral_const]
  simp only [measureReal_def, hvol, ENNReal.toReal_one, one_smul]
  rw [← hm, sub_self, mul_zero]

def physicalPositiveFactor (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N θ : ℝ) (e : Fin (D + 1)) (q : d → ℤ) (b : Bool) : Factor d (activeBlocks (d := d) ℓ h) D :=
  positiveFactor θ (physicalCenteredFactor x₀ ℓ r h k c w N e q b)

theorem physicalPositiveFactor_real (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N θ : ℝ) (e : Fin (D + 1)) (q : d → ℤ) (b : Bool)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) :
    (factorValue (Wiener.torusProjection u) (normalizedRoughChart x₀ ℓ r h k c w N ζ u) ζ
      (physicalPositiveFactor x₀ ℓ r h k c w N θ e q b)).im = 0 :=
  positiveFactor_real θ _ _ _ ζ (centeredFactor_real e q b _ _ _ ζ)

theorem physicalPositiveFactor_integral (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N θ : ℝ) (hc : 0 < c) (e : Fin (D + 1)) (q : d → ℤ) (b : Bool)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    (∫ u in Set.Icc (0 : d → ℝ) 1, (factorValue (Wiener.torusProjection u)
      (normalizedRoughChart x₀ ℓ r h k c w N ζ u) ζ (physicalPositiveFactor x₀ ℓ r h k c w N θ e q b)).re) = 1 := by
  have hvol : volume (Set.Icc (0 : d → ℝ) 1) = 1 := by simp [Real.volume_Icc_pi]
  have hconst : IntegrableOn (fun _ : d → ℝ => (1 : ℝ)) (Set.Icc 0 1) :=
    integrableOn_const.mpr (Or.inr (by simp [hvol]))
  have hi : IntegrableOn (fun u => (factorValue (Wiener.torusProjection u)
      (normalizedRoughChart x₀ ℓ r h k c w N ζ u) ζ
        (physicalCenteredFactor x₀ ℓ r h k c w N e q b)).re) (Set.Icc (0 : d → ℝ) 1) :=
    (physicalCenteredFactor_continuous x₀ ℓ r h k c w N hc e q b ζ).continuousOn.integrableOn_compact
      isCompact_Icc
  simp only [physicalPositiveFactor, positiveFactor_value, Complex.add_re, Complex.one_re,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [integral_add hconst (hi.const_mul θ), integral_const_mul, physicalCenteredFactor_integral _ _ _ _ _ _ _ _ hc]
  simp [setIntegral_const, measureReal_def, hvol]

theorem physicalPositiveFactor_bounds (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ θ : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hθ : |θ| < 1)
    (e : Fin (D + 1)) (q : d → ℤ) (b : Bool) :
    ‖physicalPositiveFactor x₀ ℓ r h k c w N θ e q b‖ ≤ 1 + |θ| ∧
      (∀ ζ u, 0 < (factorValue (Wiener.torusProjection u) (normalizedRoughChart x₀ ℓ r h k c w N ζ u) ζ
        (physicalPositiveFactor x₀ ℓ r h k c w N θ e q b)).re) ∧
      ∀ j : activeBlocks (d := d) ℓ h,
        ‖factorSymbol j (physicalPositiveFactor x₀ ℓ r h k c w N θ e q b)‖ ≤
          (|θ| / 2) * ((e.val / N₀) * (ℓ / (2 * r)) ^ Fintype.card d) := by
  obtain ⟨ha, hs⟩ := normalizedTrigCenter_bounds x₀ ℓ r h k c w N N₀ hℓ hr hc hN₀ hN hm hrough e.val q b
  have hcenter := centeredFactor_norm e q b _ ha
  refine ⟨positiveFactor_norm θ _ hcenter, fun ζ u => ?_, fun j => ?_⟩
  · have hz := normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ u
    exact (sub_pos.mpr hθ).trans_le (positiveFactor_range θ _ hcenter _ _ hz ζ).1
  · rw [physicalPositiveFactor, positiveFactor_symbol]
    have hcs := centeredFactor_symbol_bound (d := d) j e q b
      (normalizedTrigCenter x₀ ℓ r h k c w N e.val q b)
    calc
      _ ≤ |θ| * ((1 / 2) * ‖Walsh.symbolPart j (normalizedTrigCenter x₀ ℓ r h k c w N e.val q b)‖) :=
        mul_le_mul_of_nonneg_left hcs (abs_nonneg _)
      _ ≤ |θ| * ((1 / 2) * ((e.val / N₀) * (ℓ / (2 * r)) ^ Fintype.card d)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hs j) (by norm_num)) (abs_nonneg _)
      _ = _ := by ring

end CausalLowerbound.PartC

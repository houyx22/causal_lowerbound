import CausalLowerbound.PartC.MixedModels

/-! Uniform legality of both actual mixed families. Every constant is
derived from the fixed finite coefficient support and smooth profiles. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ContDiff
namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

theorem exists_roughPropensity_legal_amplitude {Q : ℕ}
    (U : Ω → CoefficientExponent d Q → ℝ) (α β γ : Regularity)
    (Lπ L₀ Lτ κ : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀)
    (hLτ : 0 < Lτ) (hκ : κ < 1 / 4) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ c : ℝ, 0 ≤ c → c ≤ ε →
      ∀ (side : Bool) (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω)
        (x₀ : d → ℝ) (ℓ r h t : ℝ), 0 < ℓ → ℓ ≤ r → r ≤ h → h ≤ 1 →
        0 ≤ t → t ≤ 1 → ℓ ^ α.exponent * r ^ β.exponent * t = h ^ γ.exponent →
        ∀ ζ : activeBlocks (d := d) ℓ h → Bool,
          (roughPropensityFields side S (fun k => U (sample k)) x₀ ℓ r h
            (c * ℓ ^ α.exponent) (c * r ^ β.exponent) t ζ).Legal α β γ Lπ L₀ Lτ κ := by
  obtain ⟨A, hA, ha⟩ := physicalRoughField_amplitude_holder (d := d)
    α.order α.fraction α.nonneg α.le_one
  obtain ⟨B, hB, hb⟩ := normalizedPropensityOutcome_scale_control U (β.order + 1)
  obtain ⟨D, hD, hd⟩ := balanced_target_holder (d := d) γ.order γ.fraction γ.nonneg γ.le_one
  obtain ⟨ε, he, he1, hbudget⟩ := exists_coded_amplitude A (2 * B) D Lπ L₀ Lτ
    hA (by positivity) hD hLπ hL₀ hLτ
  refine ⟨ε, he, he1, fun c hc hce side S sample x₀ ℓ r h t hℓ hℓr hrh hh1 ht ht1 hbal ζ => ?_⟩
  have hr := hℓ.trans_le hℓr
  have hh := hr.trans_le hrh
  have hr1 := hrh.trans hh1
  have hℓh := hℓr.trans hrh
  have hℓ1 := hℓh.trans hh1
  have hc1 := hce.trans he1
  have hja0 : 0 ≤ c * ℓ ^ α.exponent := mul_nonneg hc (Real.rpow_nonneg hℓ.le _)
  have hja1 : c * ℓ ^ α.exponent ≤ 1 :=
    (mul_le_of_le_one_right hc (Real.rpow_le_one hℓ.le hℓ1 α.exponent_nonneg)).trans hc1
  have hp := ha x₀ ℓ h c hℓ hℓh hℓ1 hc ζ
  have hs := hb side S sample x₀ r h (c * ℓ ^ α.exponent) t hr hrh hja0 hja1 ht ht1
  have hy := hs.amplitude_holder β.nonneg β.le_one hr hr1 c hc
  have heq : (c * ℓ ^ α.exponent) * (c * r ^ β.exponent) * t = c * c * h ^ γ.exponent := by
    rw [← hbal]
    ring
  rcases hbudget c hc hce with ⟨hπ, hyL, htL, hpv, hyv, hcc⟩
  unfold roughPropensityFields
  refine codedFields_legal side _ _ _ α β γ (A * c) (2 * B * c) (D * (c * c))
    Lπ L₀ Lτ κ hp hy ?_ (contDiff_const.mul (physicalRoughField_smooth _ _ _ _))
    (contDiff_const.mul hs.smooth) hπ hyL htL hLτ.le hpv hyv ?_ hκ
  · rw [heq]
    exact hd x₀ h (c * c) hh hh1 (mul_nonneg hc hc)
  · intro x
    rw [heq]
    apply (targetField_abs_le _ _ _ _).trans
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hc hc) (Real.rpow_nonneg hh.le _))]
    exact (mul_le_of_le_one_right (mul_nonneg hc hc)
      (Real.rpow_le_one hh.le hh1 γ.exponent_nonneg)).trans hcc

theorem exists_roughOutcome_legal_amplitude {Q : ℕ}
    (U : Ω → CoefficientExponent d Q → ℝ) (α β γ : Regularity)
    (Lπ L₀ Lτ κ : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀)
    (hLτ : 0 < Lτ) (hκ : κ < 1 / 4) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ c : ℝ, 0 ≤ c → c ≤ ε →
      ∀ (side : Bool) (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω)
        (x₀ : d → ℝ) (ℓ r h t : ℝ), 0 < ℓ → ℓ ≤ r → r ≤ h → h ≤ 1 →
        0 ≤ t → t ≤ 1 → r ^ α.exponent * t * ℓ ^ β.exponent = h ^ γ.exponent →
        ∀ ζ : activeBlocks (d := d) ℓ h → Bool,
          (roughOutcomeFields side S (fun k => U (sample k)) x₀ ℓ r h
            (c * r ^ α.exponent) (c * ℓ ^ β.exponent) t ζ).Legal α β γ Lπ L₀ Lτ κ := by
  obtain ⟨A, hA, ha⟩ := carriedField_amplitude_holder U α.order α.fraction α.nonneg α.le_one
  obtain ⟨B, hB, hb⟩ := normalizedRoughOutcome_scale_control U (β.order + 1)
  obtain ⟨D, hD, hd⟩ := balanced_target_holder (d := d) γ.order γ.fraction γ.nonneg γ.le_one
  obtain ⟨ε, he, he1, hbudget⟩ := exists_coded_amplitude A (2 * B) D Lπ L₀ Lτ
    hA (by positivity) hD hLπ hL₀ hLτ
  refine ⟨ε, he, he1, fun c hc hce side S sample x₀ ℓ r h t hℓ hℓr hrh hh1 ht ht1 hbal ζ => ?_⟩
  have hr := hℓ.trans_le hℓr
  have hh := hr.trans_le hrh
  have hr1 := hrh.trans hh1
  have hℓ1 := hℓr.trans hr1
  have hc1 := hce.trans he1
  have ha0 : 0 ≤ c * r ^ α.exponent := mul_nonneg hc (Real.rpow_nonneg hr.le _)
  have ha1 : c * r ^ α.exponent ≤ 1 :=
    (mul_le_of_le_one_right hc (Real.rpow_le_one hr.le hr1 α.exponent_nonneg)).trans hc1
  have hja0 : 0 ≤ (c * r ^ α.exponent) * t := mul_nonneg ha0 ht
  have hja1 : (c * r ^ α.exponent) * t ≤ 1 := (mul_le_of_le_one_right ha0 ht1).trans ha1
  have hp := ha S sample x₀ r c hr hr1 hc
  have hs := hb side S sample x₀ ℓ r h (c * r ^ α.exponent) ((c * r ^ α.exponent) * t)
    hℓ hℓr hrh ha0 ha1 hja0 hja1 ζ
  have hy := hs.amplitude_holder β.nonneg β.le_one hℓ hℓ1 c hc
  have heq : (c * r ^ α.exponent) * t * (c * ℓ ^ β.exponent) = c * c * h ^ γ.exponent := by
    rw [← hbal]
    ring
  rcases hbudget c hc hce with ⟨hπ, hyL, htL, hpv, hyv, hcc⟩
  unfold roughOutcomeFields
  refine codedFields_legal side _ _ _ α β γ (A * c) (2 * B * c) (D * (c * c))
    Lπ L₀ Lτ κ hp hy ?_ (contDiff_const.mul (carriedField_smooth _ _ _ _))
    (contDiff_const.mul hs.smooth) hπ hyL htL hLτ.le hpv hyv ?_ hκ
  · rw [heq]
    exact hd x₀ h (c * c) hh hh1 (mul_nonneg hc hc)
  · intro x
    rw [heq]
    apply (targetField_abs_le _ _ _ _).trans
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hc hc) (Real.rpow_nonneg hh.le _))]
    exact (mul_le_of_le_one_right (mul_nonneg hc hc)
      (Real.rpow_le_one hh.le hh1 γ.exponent_nonneg)).trans hcc

end CausalLowerbound.PartC

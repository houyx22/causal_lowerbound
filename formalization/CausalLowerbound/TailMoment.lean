import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake

/-! A uniform moment bound from an integrable power tail. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace CausalLowerbound

def tailEnvelope (C κ : ℝ) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => 1) t +
    (Ioi (1 : ℝ)).indicator (fun t => C * t ^ (-κ)) t

theorem tailEnvelope_nonneg (C κ : ℝ) (hC : 0 ≤ C) (t : ℝ) :
    0 ≤ tailEnvelope C κ t := by
  apply add_nonneg
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · apply Set.indicator_nonneg _ t
    intro t ht
    have ht' : 1 < t := ht
    exact mul_nonneg hC (Real.rpow_nonneg (by linarith : 0 ≤ t) _)

theorem tailEnvelope_integrable (C κ : ℝ) (hκ : 1 < κ) :
    Integrable (tailEnvelope C κ) volume := by
  have h₁ : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 1) :=
    integrableOn_const.mpr (Or.inr (by simp))
  have h₂ : IntegrableOn (fun t : ℝ => C * t ^ (-κ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -κ < -1) (by norm_num : (0 : ℝ) < 1)).const_mul C
  exact ((integrable_indicator_iff measurableSet_Ioc).mpr h₁).add
    ((integrable_indicator_iff measurableSet_Ioi).mpr h₂)

def tailMomentBound (C κ : ℝ) : ℝ := ∫ t : ℝ, tailEnvelope C κ t

theorem tailMomentBound_nonneg (C κ : ℝ) (hC : 0 ≤ C) : 0 ≤ tailMomentBound C κ :=
  integral_nonneg (tailEnvelope_nonneg C κ hC)

theorem integrable_of_power_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (C κ : ℝ) (hC : 0 ≤ C) (hκ : 1 < κ)
    (htail : ∀ t : ℝ, 1 < t → μ {x | t < f x} ≤ ENNReal.ofReal (C * t ^ (-κ))) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ≤ tailMomentBound C κ := by
  have he := tailEnvelope_integrable C κ hκ
  have he0 : 0 ≤ᵐ[volume] tailEnvelope C κ :=
    Filter.Eventually.of_forall (tailEnvelope_nonneg C κ hC)
  have hf0ae : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall hf0
  have hbound : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤
      ∫⁻ t : ℝ, ENNReal.ofReal (tailEnvelope C κ t) := by
    rw [lintegral_eq_lintegral_meas_lt μ hf0ae hf.aemeasurable]
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tailEnvelope C κ t) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        by_cases h : 1 < t
        · have hm : t ∈ Ioi (1 : ℝ) := h
          simpa [tailEnvelope, Set.indicator_of_mem hm, show t ∉ Ioc (0 : ℝ) 1 by
            intro hh; linarith [hh.2]] using htail t h
        · have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, le_of_not_gt h⟩
          have hn : t ∉ Ioi (1 : ℝ) := h
          simpa [tailEnvelope, Set.indicator_of_mem hm, Set.indicator_of_not_mem hn] using
            (prob_le_one (μ := μ) (s := {x | t < f x}))
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
  have hfinite : (∫⁻ t : ℝ, ENNReal.ofReal (tailEnvelope C κ t)) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal he0).mp he.hasFiniteIntegral
  have hi : Integrable f μ := ⟨hf.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hf0ae).mpr (hbound.trans_lt hfinite)⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hf0ae hi.aestronglyMeasurable,
    tailMomentBound, integral_eq_lintegral_of_nonneg_ae he0 he.aestronglyMeasurable]
  exact ENNReal.toReal_mono hfinite.ne hbound

end CausalLowerbound

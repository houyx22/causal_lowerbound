import CausalLowerbound.FiniteConditionalExperiment
import CausalLowerbound.FiniteTesting

/-! Le Cam's absolute-loss bound on an arbitrary dominated sample space.
Risks take values in ENNReal, so estimators with infinite risk are included. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace CausalLowerbound
variable {X : Type*} [MeasurableSpace X]

structure DensityLaw (μ : Measure X) where
  density : X → ℝ
  nonneg : ∀ x, 0 ≤ density x
  measurable : Measurable density
  integrable : Integrable density μ
  total : (∫ x, density x ∂μ) = 1

namespace DensityLaw
variable {μ : Measure X}
def toMeasure (P : DensityLaw μ) : Measure X := μ.withDensity (fun x => ENNReal.ofReal (P.density x))
def totalVariation (P Q : DensityLaw μ) : ℝ := (∫ x, |P.density x - Q.density x| ∂μ) / 2
def risk (P : DensityLaw μ) (est : X → ℝ) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal |est x - θ| ∂P.toMeasure

instance (P : DensityLaw μ) : IsProbabilityMeasure P.toMeasure := by
  constructor
  rw [toMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal P.integrable (Filter.Eventually.of_forall P.nonneg),
    P.total, ENNReal.ofReal_one]

theorem risk_eq (P : DensityLaw μ) (est : X → ℝ) (he : Measurable est) (θ : ℝ) :
    P.risk est θ = ∫⁻ x, ENNReal.ofReal (P.density x * |est x - θ|) ∂μ := by
  have hme : Measurable (fun x => ENNReal.ofReal |est x - θ|) :=
    (continuous_abs.measurable.comp (he.sub measurable_const)).ennreal_ofReal
  rw [risk, toMeasure, lintegral_withDensity_eq_lintegral_mul μ P.measurable.ennreal_ofReal
    hme]
  apply lintegral_congr
  intro x
  exact (ENNReal.ofReal_mul (P.nonneg x)).symm

theorem totalVariation_nonneg (P Q : DensityLaw μ) : 0 ≤ P.totalVariation Q :=
  div_nonneg (integral_nonneg (fun _ => abs_nonneg _)) (by norm_num)

theorem totalVariation_le_one (P Q : DensityLaw μ) : P.totalVariation Q ≤ 1 := by
  have hs : Integrable (fun x => P.density x + Q.density x) μ := P.integrable.add Q.integrable
  have ha : Integrable (fun x => |P.density x - Q.density x|) μ := (P.integrable.sub Q.integrable).abs
  have h := integral_mono ha hs
    (fun x => (abs_sub (P.density x) (Q.density x)).trans_eq
      (by rw [abs_of_nonneg (P.nonneg x), abs_of_nonneg (Q.nonneg x)]))
  rw [integral_add P.integrable Q.integrable, P.total, Q.total] at h
  unfold totalVariation
  linarith

theorem overlap_integrable (P Q : DensityLaw μ) : Integrable (fun x => min (P.density x) (Q.density x)) μ := by
  apply P.integrable.mono' (P.measurable.min Q.measurable).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (P.nonneg x) (Q.nonneg x))]
  exact min_le_left _ _

theorem overlap_identity (P Q : DensityLaw μ) :
    (∫ x, min (P.density x) (Q.density x) ∂μ) = 1 - P.totalVariation Q := by
  have he (x : X) : 2 * min (P.density x) (Q.density x) =
      P.density x + Q.density x - |P.density x - Q.density x| := by
    rcases le_total (P.density x) (Q.density x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  have hh := integral_congr_ae (μ := μ) (Filter.Eventually.of_forall he)
  have hs : Integrable (fun x => P.density x + Q.density x) μ := P.integrable.add Q.integrable
  have ha : Integrable (fun x => |P.density x - Q.density x|) μ := (P.integrable.sub Q.integrable).abs
  rw [integral_const_mul, integral_sub hs ha,
    integral_add P.integrable Q.integrable, P.total, Q.total] at hh
  unfold totalVariation
  linarith

theorem two_point_sum_risk (P Q : DensityLaw μ) (est : X → ℝ) (he : Measurable est)
    (θ₀ θ₁ : ℝ) (hθ : θ₀ ≤ θ₁) :
    ENNReal.ofReal ((θ₁ - θ₀) * (1 - P.totalVariation Q)) ≤ P.risk est θ₁ + Q.risk est θ₀ := by
  have hpoint (x : X) : min (P.density x) (Q.density x) * (θ₁ - θ₀) ≤
      P.density x * |est x - θ₁| + Q.density x * |est x - θ₀| := by
    have ht := abs_sub_le θ₁ (est x) θ₀
    rw [abs_of_nonneg (sub_nonneg.mpr hθ), abs_sub_comm θ₁ (est x)] at ht
    calc
      _ ≤ min (P.density x) (Q.density x) * (|est x - θ₁| + |est x - θ₀|) :=
        mul_le_mul_of_nonneg_left ht (le_min (P.nonneg x) (Q.nonneg x))
      _ ≤ _ := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _))
  have hl : (∫⁻ x, ENNReal.ofReal (min (P.density x) (Q.density x) * (θ₁ - θ₀)) ∂μ) =
      ENNReal.ofReal ((θ₁ - θ₀) * (1 - P.totalVariation Q)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal ((overlap_integrable P Q).mul_const _)
      (Filter.Eventually.of_forall (fun x => mul_nonneg (le_min (P.nonneg x) (Q.nonneg x)) (sub_nonneg.mpr hθ))),
      integral_mul_const, overlap_identity, mul_comm]
  have hme : Measurable (fun x => ENNReal.ofReal (P.density x * |est x - θ₁|)) :=
    (P.measurable.mul (continuous_abs.measurable.comp (he.sub measurable_const))).ennreal_ofReal
  rw [← hl, risk_eq P est he, risk_eq Q est he, ← lintegral_add_left hme]
  apply lintegral_mono
  intro x
  dsimp only
  rw [← ENNReal.ofReal_add (mul_nonneg (P.nonneg x) (abs_nonneg _))
    (mul_nonneg (Q.nonneg x) (abs_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (hpoint x)

/-- The exact separation/2 constant, for all measurable estimators,
including those with infinite loss. -/
theorem two_point_absolute_loss (P Q : DensityLaw μ) (est : X → ℝ) (he : Measurable est)
    (θ₀ θ₁ : ℝ) (hθ : θ₀ ≤ θ₁) :
    ENNReal.ofReal ((θ₁ - θ₀) / 2 * (1 - P.totalVariation Q)) ≤
      max (P.risk est θ₁) (Q.risk est θ₀) := by
  have h := two_point_sum_risk P Q est he θ₀ θ₁ hθ
  have hm := add_le_add (le_max_left (P.risk est θ₁) (Q.risk est θ₀))
    (le_max_right (P.risk est θ₁) (Q.risk est θ₀))
  have hc : (θ₁ - θ₀) / 2 * (1 - P.totalVariation Q) =
      ((θ₁ - θ₀) * (1 - P.totalVariation Q)) / 2 := by ring
  rw [hc, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num only [ENNReal.ofReal_ofNat]
  apply (ENNReal.div_le_iff (by norm_num) (by simp)).mpr
  simpa only [mul_two] using h.trans hm

theorem two_point_quarter (P Q : DensityLaw μ) (est : X → ℝ) (he : Measurable est)
    (θ₀ θ₁ : ℝ) (hθ : θ₀ ≤ θ₁) (htv : P.totalVariation Q ≤ 1 / 2) :
    ENNReal.ofReal ((θ₁ - θ₀) / 4) ≤ max (P.risk est θ₁) (Q.risk est θ₀) := by
  apply le_trans _ (two_point_absolute_loss P Q est he θ₀ θ₁ hθ)
  apply ENNReal.ofReal_le_ofReal
  nlinarith [mul_nonneg (sub_nonneg.mpr hθ) (show 0 ≤ 1 / 2 - P.totalVariation Q by linarith)]

end DensityLaw
end CausalLowerbound

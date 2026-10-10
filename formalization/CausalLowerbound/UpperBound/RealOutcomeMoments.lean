import CausalLowerbound.UpperBound.RealOutcomeModel

/-! Conditional second moments imply the actual observation-law L² bounds.
The response remains real-valued and can have unbounded support. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Classical

namespace CausalLowerbound.UpperBound.RealOutcomeModel

variable {d : Type*} [Fintype d] {ε lower upper M₂ : ℝ}
variable (M : RealOutcomeModel d ε lower upper M₂)

theorem conditional_secondMoment_integrable :
    Integrable (fun x => ∫ z, z.2 ^ 2 ∂M.conditional x) M.design := by
  have hm : StronglyMeasurable (fun x => ∫ z, z.2 ^ 2 ∂M.conditional x) :=
    (measurable_snd.pow_const 2).stronglyMeasurable.integral_kernel
  apply Integrable.mono' (integrable_const M₂) hm.aestronglyMeasurable
  filter_upwards [M.response_second_moment] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun z => sq_nonneg z.2))]
  exact hx

theorem observation_response_square_integrable :
    Integrable (fun z : (d → ℝ) × (Bool × ℝ) => z.2.2 ^ 2) M.observationLaw := by
  have hm : AEStronglyMeasurable (fun z : (d → ℝ) × (Bool × ℝ) => z.2.2 ^ 2)
      (M.design ⊗ₘ M.conditional) :=
    ((measurable_snd.comp measurable_snd).pow_const 2).aestronglyMeasurable
  apply (Measure.integrable_compProd_iff hm).mpr
  constructor
  · exact M.response_memLp.mono (fun _ h => h.integrable_sq)
  · simpa only [Real.norm_eq_abs, abs_sq] using M.conditional_secondMoment_integrable

theorem observation_response_memLp :
    MemLp (fun z : (d → ℝ) × (Bool × ℝ) => z.2.2) 2 M.observationLaw :=
  (memLp_two_iff_integrable_sq
    (measurable_snd.comp measurable_snd).aestronglyMeasurable).mpr
    M.observation_response_square_integrable

theorem observation_response_second_moment :
    (∫ z : (d → ℝ) × (Bool × ℝ), z.2.2 ^ 2 ∂M.observationLaw) ≤ M₂ := by
  calc
    _ = ∫ x, ∫ z, z.2 ^ 2 ∂M.conditional x ∂M.design :=
      Measure.integral_compProd M.observation_response_square_integrable
    _ ≤ ∫ _x, M₂ ∂M.design := integral_mono_ae M.conditional_secondMoment_integrable
      (integrable_const M₂) M.response_second_moment
    _ = M₂ := by simp

theorem observation_treatment_memLp :
    MemLp (fun z : (d → ℝ) × (Bool × ℝ) => treatmentValue z.2) 2 M.observationLaw :=
  MemLp.of_bound (measurable_treatmentValue.comp measurable_snd).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun z => treatmentValue_bound z.2))

theorem residual_square_bound (z : Bool × ℝ) (t : ℝ) :
    (z.2 - t * treatmentValue z) ^ 2 ≤ 2 * z.2 ^ 2 + 2 * t ^ 2 := by
  cases z with
  | mk a y =>
      cases a <;> simp only [treatmentValue, Bool.false_eq_true, ↓reduceIte, mul_zero,
        sub_zero, mul_one]
      · nlinarith [sq_nonneg y, sq_nonneg t]
      · nlinarith [sq_nonneg (y + t)]

theorem conditional_residual_second_moment_all :
    ∀ᵐ x ∂M.design, ∀ t : ℝ,
      (∫ z, (z.2 - t * treatmentValue z) ^ 2 ∂M.conditional x) ≤ 2 * M₂ + 2 * t ^ 2 := by
  filter_upwards [M.response_memLp, M.response_second_moment] with x hY hY₂
  intro t
  have hR := hY.sub ((treatmentValue_memLp (M.conditional x)).const_mul t)
  calc
    _ ≤ ∫ z, 2 * z.2 ^ 2 + 2 * t ^ 2 ∂M.conditional x :=
      integral_mono hR.integrable_sq ((hY.integrable_sq.const_mul 2).add (integrable_const _))
        (fun z => residual_square_bound z t)
    _ = 2 * (∫ z, z.2 ^ 2 ∂M.conditional x) + 2 * t ^ 2 := by
      rw [integral_add (hY.integrable_sq.const_mul 2) (integrable_const _), integral_const_mul]
      simp
    _ ≤ _ := by linarith

theorem conditional_residual_second_moment (t : ℝ) :
    ∀ᵐ x ∂M.design,
      (∫ z, (z.2 - t * treatmentValue z) ^ 2 ∂M.conditional x) ≤ 2 * M₂ + 2 * t ^ 2 :=
  M.conditional_residual_second_moment_all.mono (fun _ hx => hx t)

end CausalLowerbound.UpperBound.RealOutcomeModel

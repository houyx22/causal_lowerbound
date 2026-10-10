import CausalLowerbound.UpperBound.SplitSample

/-! A support-sensitive second-moment bound for partial kernels.  Cauchy--Schwarz
is applied only on the accepted completions.  Thus a completion-probability
bound and one full-kernel second moment control every overlap projection. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {Ω : Type*} [MeasurableSpace Ω]

theorem square_integral_le_mass_mul_square (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Integrable f μ) (hf₂ : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ x, f x ^ 2 ∂μ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  letI : NeZero μ := ⟨hμ⟩
  let b := μ.real Set.univ
  let a := ∫ x, f x ∂μ
  have hb : 0 < b := measureReal_univ_pos
  have he : (∫ x, (b * f x - a) ^ 2 ∂μ) =
      b * (b * (∫ x, f x ^ 2 ∂μ) - a ^ 2) := by
    have hexp (x : Ω) : (b * f x - a) ^ 2 =
        (b ^ 2 * f x ^ 2 - (2 * b * a) * f x) + a ^ 2 := by ring
    simp_rw [hexp]
    rw [integral_add (f := fun x => b ^ 2 * f x ^ 2 - (2 * b * a) * f x)
        ((hf₂.const_mul _).sub (hf.const_mul _)) (integrable_const _),
      integral_sub (f := fun x => b ^ 2 * f x ^ 2)
        (hf₂.const_mul _) (hf.const_mul _), integral_const_mul,
      integral_const_mul, integral_const]
    change b ^ 2 * (∫ x, f x ^ 2 ∂μ) - (2 * b * a) * a + b * a ^ 2 = _
    ring
  have hn := integral_nonneg (μ := μ) (fun x : Ω => sq_nonneg (b * f x - a))
  rw [he] at hn
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hb).mp hn)

theorem square_integral_le_support_mass_mul_square (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : Set Ω) (f : Ω → ℝ) (hf : Integrable f μ)
    (hf₂ : Integrable (fun x => f x ^ 2) μ) (hs : ∀ x, x ∉ E → f x = 0) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real E * ∫ x, f x ^ 2 ∂μ := by
  have h := square_integral_le_mass_mul_square (μ.restrict E) f
    hf.integrableOn hf₂.integrableOn
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hs,
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hs x hx, zero_pow (by decide : 2 ≠ 0)])] at h
  simpa only [Measure.real, Measure.restrict_apply_univ] using h

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem partialKernel_secondMoment_le_completion_mass
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : A × B → ℝ} (hK : MemLp K 2 (μ.prod ν)) (E : Set (A × B))
    (hs : ∀ z, z ∉ E → K z = 0) {c : ℝ}
    (hc : ∀ᵐ a ∂μ, ν.real {b | (a, b) ∈ E} ≤ c) :
    (∫ a, partialKernel ν K a ^ 2 ∂μ) ≤ c * ∫ z, K z ^ 2 ∂μ.prod ν := by
  rw [integral_prod _ hK.integrable_sq, ← integral_const_mul]
  apply integral_mono_ae (partialKernel_memLp μ ν hK).integrable_sq
    (hK.integrable_sq.integral_prod_left.const_mul c)
  filter_upwards [(hK.integrable one_le_two).prod_right_ae,
    hK.integrable_sq.prod_right_ae, hc] with a ha ha₂ hca
  exact (square_integral_le_support_mass_mul_square ν {b | (a, b) ∈ E}
    (fun b => K (a, b)) ha ha₂ (fun b hb => hs (a, b) hb)).trans
    (mul_le_mul_of_nonneg_right hca (integral_nonneg (fun b => sq_nonneg (K (a, b)))))

theorem roleProjection_secondMoment_le_completion_mass
    {I Z : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] {K : (I → Z) → ℝ}
    (hK : MemLp K 2 (Measure.pi (fun _ : I => μ))) (E : Set (I → Z))
    (hs : ∀ z, z ∉ E → K z = 0) (S : Finset I) {c : ℝ}
    (hc : ∀ᵐ x ∂Measure.pi (fun _ : {i // i ∈ S} => μ),
      (Measure.pi (fun _ : {i // i ∉ S} => μ)).real
        {y | joinRoles S (x, y) ∈ E} ≤ c) :
    (∫ x, roleProjection μ K S x ^ 2 ∂Measure.pi (fun _ : {i // i ∈ S} => μ)) ≤
      c * ∫ z, K z ^ 2 ∂Measure.pi (fun _ : I => μ) := by
  have hsplit := joinRoles_measurePreserving μ S
  have h := partialKernel_secondMoment_le_completion_mass _ _
    (hK.comp_measurePreserving hsplit) (joinRoles S ⁻¹' E)
    (fun z hz => hs (joinRoles S z) hz) hc
  simp only [Function.comp_apply] at h
  rw [integral_comp_measurePreserving hsplit
    (f := fun z => K z ^ 2) (hK.aestronglyMeasurable.pow 2)] at h
  exact h

end CausalLowerbound.UpperBound

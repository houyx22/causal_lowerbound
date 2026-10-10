import CausalLowerbound.UpperBound.KernelMoments

/-! The acceptance mass and the normalized two-term variance estimate.
The concrete response and matrix kernels have second moments of this mass
order, with constants uniform in the three bandwidths and the target. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

def stencilMass (p : ℕ) (T : StencilTemplate d p) (h ℓ r : ℝ) : ℝ :=
  (h / 4) ^ Fintype.card d * (fineCellVolume d ℓ).toReal *
    (coarseCellVolume p T r).toReal ^ (Fintype.card (StencilRole d p) - 2)

theorem fineCellVolume_toReal {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    (fineCellVolume d ℓ).toReal = ℓ ^ Fintype.card d := by
  rw [fineCellVolume, ENNReal.toReal_pow, ENNReal.toReal_ofReal hℓ]

theorem coarseCellVolume_toReal (p : ℕ) (T : StencilTemplate d p) {r : ℝ} (hr : 0 ≤ r) :
    (coarseCellVolume p T r).toReal = (2 * r * T.radius) ^ Fintype.card d := by
  rw [coarseCellVolume, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (by norm_num) hr) T.radius_pos.le)]

theorem stencilMass_pos (p : ℕ) (T : StencilTemplate d p) {h ℓ r : ℝ}
    (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r) : 0 < stencilMass p T h ℓ r := by
  rw [stencilMass, fineCellVolume_toReal hℓ.le, coarseCellVolume_toReal p T hr.le]
  have hδ := T.radius_pos
  positivity

theorem acceptedStencil_volume_toReal (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r) :
    (volume (acceptedStencil p T x₀ h ℓ r)).toReal = stencilMass p T h ℓ r := by
  have hc : Fintype.card (StencilRole d p) - 2 = Fintype.card (TensorIndex d p) := by
    simp only [StencilRole, Fintype.card_option]
    omega
  rw [acceptedStencil_volume p T x₀ hh hℓ hr]
  simp only [stencilMass, fineCellVolume, coarseCellVolume, ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal (div_nonneg hh.le (by norm_num))]
  simp only [hc, pow_mul]
  ring

namespace RealOutcomeModel

variable {ε lower upper M₂ : ℝ} (M : RealOutcomeModel d ε lower upper M₂)

theorem acceptedStencil_probability_real_le_mass (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r) (hU : 0 ≤ upper) :
    (Measure.pi (fun _ : StencilRole d p => M.design)).real (acceptedStencil p T x₀ h ℓ r) ≤
      upper ^ Fintype.card (StencilRole d p) * stencilMass p T h ℓ r := by
  have hu : (Measure.pi (fun _ : StencilRole d p => M.design)) (acceptedStencil p T x₀ h ℓ r) ≤
      ENNReal.ofReal upper ^ Fintype.card (StencilRole d p) * volume (acceptedStencil p T x₀ h ℓ r) := by
    simpa only [Measure.smul_apply, ENNReal.smul_def, ENNReal.coe_pow, ENNReal.ofReal] using
      M.design_product_upper_domination (StencilRole d p) (acceptedStencil p T x₀ h ℓ r)
  have hv : volume (acceptedStencil p T x₀ h ℓ r) ≠ ⊤ := by
    rw [acceptedStencil_volume p T x₀ hh hℓ hr]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
  have he := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hv) hu
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hU,
    acceptedStencil_volume_toReal p T x₀ hh hℓ hr] using he

include M in
theorem responseSecondMoment_nonneg : 0 ≤ M₂ :=
  (integral_nonneg (fun z : (d → ℝ) × (Bool × ℝ) => sq_nonneg z.2.2)).trans
    M.observation_response_second_moment

theorem stencilResponseKernel_secondMoment_le_mass (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (hU : 0 ≤ upper) (ν : TensorIndex d p) :
    (∫ z, stencilResponseKernel p T x₀ h ℓ r ν z ^ 2 ∂M.sampleLaw (StencilRole d p)) ≤
      (2 * M₂ * (Fintype.card (StencilRole d p) : ℝ) ^ 2 * upper ^ Fintype.card (StencilRole d p)) *
        stencilMass p T h ℓ r := by
  apply (M.stencilResponseKernel_secondMoment_le p T x₀ hx hh hhsmall hℓ hℓr hrh ν).trans
  rw [mul_assoc (2 * M₂ * (Fintype.card (StencilRole d p) : ℝ) ^ 2)]
  exact mul_le_mul_of_nonneg_left
    (M.acceptedStencil_probability_real_le_mass p T x₀ hh hℓ (hℓ.trans_le hℓr) hU)
    (mul_nonneg (mul_nonneg (by norm_num) M.responseSecondMoment_nonneg) (sq_nonneg _))

theorem stencilMatrixKernel_secondMoment_le_mass (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) (hU : 0 ≤ upper) (ν ω : TensorIndex d p) :
    (∫ z, stencilMatrixKernel p T x₀ h ℓ r ν ω z ^ 2 ∂M.sampleLaw (StencilRole d p)) ≤
      ((Fintype.card (StencilRole d p) : ℝ) ^ 2 * upper ^ Fintype.card (StencilRole d p)) *
        stencilMass p T h ℓ r := by
  apply (M.stencilMatrixKernel_secondMoment_le p T x₀ hx hh hhsmall hℓ hℓr hrh ν ω).trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (M.acceptedStencil_probability_real_le_mass p T x₀ hh hℓ (hℓ.trans_le hℓr) hU) (sq_nonneg _)

theorem stencil_variance_le_mass (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    [∀ i, Nonempty (J i)] {K : (StencilRole d p → (d → ℝ) × (Bool × ℝ)) → ℝ}
    (hK : MemLp K 2 (M.sampleLaw (StencilRole d p)))
    (hs : ∀ z, z ∉ acceptedObservationStencil p T x₀ h ℓ r → K z = 0)
    {η B V : ℝ} (hU : 0 ≤ upper) (hη : 0 ≤ η) (hB : 1 ≤ B)
    (hUB : upper ≤ B) (hηC : η ≤ B * (coarseCellVolume p T r).toReal)
    (hJ : ∀ i, (Fintype.card (J i) : ℝ)⁻¹ ≤ η)
    (hV : (∫ z, K z ^ 2 ∂M.sampleLaw (StencilRole d p)) ≤ V * stencilMass p T h ℓ r) :
    variance (Measure.pi (fun _ : Σ i, J i => M.observationLaw))
        (tupleAverage (fun a => K ∘ tupleObservation a)) ≤
      ((2 : ℝ) ^ Fintype.card (StencilRole d p) * B ^ Fintype.card (StencilRole d p) * V) *
        stencilMass p T h ℓ r ^ 2 *
        (η / (h / 4) ^ Fintype.card d + η ^ 2 / ((h / 4) ^ Fintype.card d * ℓ ^ Fintype.card d)) := by
  apply (M.stencil_variance_le_two_terms p T x₀ hh hℓ hr J hK hs hU hη hB hUB hηC hJ).trans
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  calc
    _ ≤ ((2 : ℝ) ^ Fintype.card (StencilRole d p) * B ^ Fintype.card (StencilRole d p) *
        (coarseCellVolume p T r).toReal ^ (Fintype.card (StencilRole d p) - 2) *
        (η * (fineCellVolume d ℓ).toReal + η ^ 2)) * (V * stencilMass p T h ℓ r) :=
      mul_le_mul_of_nonneg_left hV (by positivity)
    _ = _ := by
      rw [stencilMass, fineCellVolume_toReal hℓ.le]
      have hh₀ : (h / 4) ^ Fintype.card d ≠ 0 := pow_ne_zero _ (div_ne_zero hh.ne' (by norm_num))
      have hℓ₀ : ℓ ^ Fintype.card d ≠ 0 := pow_ne_zero _ hℓ.ne'
      field_simp
      <;> ring

end RealOutcomeModel
end CausalLowerbound.UpperBound

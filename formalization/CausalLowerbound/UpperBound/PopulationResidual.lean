import CausalLowerbound.UpperBound.EmpiricalStatistics

/-! The population estimating-equation residual is the mean of the actual
response kernel minus the actual matrix kernel applied to a coefficient
vector.  Its conditional form is exactly the residual score. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {I F : Type*} [Fintype I] [Fintype F]

theorem featureContrast_linearCombination (w a : I → ℝ) (φ : I → F → ℝ) (θ : F → ℝ) :
    (∑ ν, (∑ i, w i * a i * φ i ν) * θ ν) =
      ∑ i, w i * a i * (∑ ν, θ ν * φ i ν) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro ν _
  ring

theorem residualScore_sub (w t : I → ℝ) (z : I → Bool × ℝ) :
    residualScore w t z = residualScore w 0 z -
      (∑ i, w i * treatmentValue (z i)) * (∑ i, w i * treatmentValue (z i) * t i) := by
  have he : coordinateContrast w (fun i u => u.2 - t i * treatmentValue u) z =
      (∑ i, w i * (z i).2) - ∑ i, w i * treatmentValue (z i) * t i := by
    simp only [coordinateContrast, mul_sub, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [residualScore, he]
  simp only [residualScore, coordinateContrast, Pi.zero_apply, zero_mul, sub_zero]
  ring

variable {d : Type*} [Fintype d]

def stencilResidualKernel (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (θ : TensorIndex d p → ℝ) (ν : TensorIndex d p)
    (z : StencilRole d p → (d → ℝ) × (Bool × ℝ)) : ℝ :=
  stencilResponseKernel p T x₀ h ℓ r ν z - ∑ ω, stencilMatrixKernel p T x₀ h ℓ r ν ω z * θ ω

theorem stencilResidualKernel_eq_score (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (θ : TensorIndex d p → ℝ) (ν : TensorIndex d p)
    (z : StencilRole d p → (d → ℝ) × (Bool × ℝ)) :
    stencilResidualKernel p T x₀ h ℓ r θ ν z =
      if z ∈ acceptedObservationStencil p T x₀ h ℓ r then
        stencilFeatureMean p x₀ h ℓ r (fun i => (z i).1) ν *
          residualScore (observedStencilWeights p x₀ ℓ r (fun i => (z i).1))
            (fun i => ∑ ω, θ ω * stencilFeature p x₀ h (fun j => (z j).1) i ω) (fun i => (z i).2)
      else 0 := by
  by_cases hz : z ∈ acceptedObservationStencil p T x₀ h ℓ r
  · simp only [stencilResidualKernel, stencilResponseKernel, stencilMatrixKernel, hz, if_true]
    rw [residualScore_sub _
      (fun i => ∑ ω, θ ω * stencilFeature p x₀ h (fun j => (z j).1) i ω) (fun i => (z i).2), mul_sub]
    congr 1
    have he := featureContrast_linearCombination
      (observedStencilWeights p x₀ ℓ r (fun i => (z i).1)) (fun i => treatmentValue (z i).2)
      (fun i ω => stencilFeature p x₀ h (fun j => (z j).1) i ω) θ
    have hs (c : ℝ) (f g : TensorIndex d p → ℝ) :
        (∑ ω, c * f ω * g ω) = c * ∑ ω, f ω * g ω := by
      simp only [mul_assoc, Finset.mul_sum]
    rw [← mul_assoc, ← he]
    exact hs _ _ _
  · simp only [stencilResidualKernel, stencilResponseKernel, stencilMatrixKernel, hz,
      if_false, zero_mul, Finset.sum_const_zero, sub_zero]

theorem stencilResidualKernel_measurable (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (θ : TensorIndex d p → ℝ) (ν : TensorIndex d p) :
    Measurable (stencilResidualKernel p T x₀ h ℓ r θ ν) :=
  (stencilResponseKernel_measurable p T x₀ h ℓ r ν).sub
    (Finset.measurable_sum Finset.univ (fun ω _ =>
      (stencilMatrixKernel_measurable p T x₀ h ℓ r ν ω).mul measurable_const))

namespace RealOutcomeModel

variable {ε lower upper M₂ : ℝ} (M : RealOutcomeModel d ε lower upper M₂)

def stencilPopulationResponse (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ) :
    TensorIndex d p → ℝ :=
  fun ν => ∫ z, stencilResponseKernel p T x₀ h ℓ r ν z ∂M.sampleLaw (StencilRole d p)

def stencilPopulationMatrix (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ) :
    Matrix (TensorIndex d p) (TensorIndex d p) ℝ :=
  fun ν ω => ∫ z, stencilMatrixKernel p T x₀ h ℓ r ν ω z ∂M.sampleLaw (StencilRole d p)

theorem stencilResidualKernel_memLp (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (θ : TensorIndex d p → ℝ) (ν : TensorIndex d p) :
    MemLp (stencilResidualKernel p T x₀ h ℓ r θ ν) 2 (M.sampleLaw (StencilRole d p)) :=
  (M.stencilResponseKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh ν).sub
    (memLp_finset_sum _ (fun ω _ => by
      simpa only [mul_comm] using
        (M.stencilMatrixKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh ν ω).const_mul (θ ω)))

theorem stencilPopulationResidual_integral (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (θ : TensorIndex d p → ℝ) (ν : TensorIndex d p) :
    (∫ z, stencilResidualKernel p T x₀ h ℓ r θ ν z ∂M.sampleLaw (StencilRole d p)) =
      M.stencilPopulationResponse p T x₀ h ℓ r ν -
        ∑ ω, M.stencilPopulationMatrix p T x₀ h ℓ r ν ω * θ ω := by
  have hQ (ω : TensorIndex d p) :=
    ((M.stencilMatrixKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh ν ω).integrable one_le_two).mul_const (θ ω)
  unfold stencilResidualKernel
  rw [integral_sub ((M.stencilResponseKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh ν).integrable one_le_two)
    (integrable_finset_sum Finset.univ (fun ω _ => hQ ω)),
    integral_finset_sum Finset.univ (fun ω _ => hQ ω)]
  simp only [integral_mul_const, stencilPopulationResponse, stencilPopulationMatrix]

theorem empiricalStencilResponse_mean (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] [∀ i, Nonempty (J i)] (ν : TensorIndex d p) :
    (∫ z, empiricalStencilResponse p T x₀ h ℓ r J z ν
      ∂Measure.pi (fun _ : Σ i, J i => M.observationLaw)) = M.stencilPopulationResponse p T x₀ h ℓ r ν :=
  integral_splitSample M.observationLaw
    ((M.stencilResponseKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh ν).integrable one_le_two)

theorem empiricalStencilMatrix_mean (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] [∀ i, Nonempty (J i)] (ν ω : TensorIndex d p) :
    (∫ z, empiricalStencilMatrix p T x₀ h ℓ r J z ν ω
      ∂Measure.pi (fun _ : Σ i, J i => M.observationLaw)) = M.stencilPopulationMatrix p T x₀ h ℓ r ν ω :=
  integral_splitSample M.observationLaw
    ((M.stencilMatrixKernel_memLp p T x₀ hx hh hhsmall hℓ hℓr hrh ν ω).integrable one_le_two)

end RealOutcomeModel
end CausalLowerbound.UpperBound

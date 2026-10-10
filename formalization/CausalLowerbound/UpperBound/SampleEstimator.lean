import CausalLowerbound.UpperBound.BalancedSample
import CausalLowerbound.UpperBound.MeasurableEstimator

/-! The estimator as a measurable function of the original n observations,
with exact squared- and absolute-risk transfer to the disjoint role groups. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

theorem empiricalStencilEstimate_memLp (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (J : StencilRole d p → Type*) [∀ i, Fintype (J i)]
    {κ L : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L)
    (μ : Measure ((Σ i, J i) → (d → ℝ) × (Bool × ℝ))) [IsFiniteMeasure μ] :
    MemLp (empiricalStencilEstimate p T x₀ h ℓ r J κ hκ L) 2 μ := by
  apply MemLp.of_bound (empiricalStencilEstimate_measurable p T x₀ h ℓ r J hκ L).aestronglyMeasurable L
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs]
  exact abs_le.mpr (clip_mem _ _ hL)

def sampleStencilEstimate (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (n : ℕ) (κ : ℝ) (hκ : 0 < κ) (L : ℝ)
    (z : Fin n → (d → ℝ) × (Bool × ℝ)) : ℝ :=
  empiricalStencilEstimate p T x₀ h ℓ r
    (fun _ => Fin (balancedGroupSize (StencilRole d p) n)) κ hκ L
    (balancedSample (StencilRole d p) n z)

theorem sampleStencilEstimate_measurable (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (n : ℕ) {κ : ℝ} (hκ : 0 < κ) (L : ℝ) :
    Measurable (sampleStencilEstimate p T x₀ h ℓ r n κ hκ L) :=
  (empiricalStencilEstimate_measurable p T x₀ h ℓ r _ hκ L).comp
    (balancedSample_measurable (StencilRole d p) n)

theorem sampleStencilEstimate_mse_eq (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (n : ℕ) {κ : ℝ} (hκ : 0 < κ) (L τ : ℝ)
    (μ : Measure ((d → ℝ) × (Bool × ℝ))) [IsProbabilityMeasure μ] :
    (∫ z, (sampleStencilEstimate p T x₀ h ℓ r n κ hκ L z - τ) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ z, (empiricalStencilEstimate p T x₀ h ℓ r
        (fun _ => Fin (balancedGroupSize (StencilRole d p) n)) κ hκ L z - τ) ^ 2
        ∂Measure.pi (fun _ : Σ _ : StencilRole d p, Fin (balancedGroupSize (StencilRole d p) n) => μ) :=
  integral_balancedSample (StencilRole d p) μ n
    (((empiricalStencilEstimate_measurable p T x₀ h ℓ r _ hκ L).sub measurable_const).pow_const 2).aestronglyMeasurable

theorem sampleStencilEstimate_mae_eq (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (n : ℕ) {κ : ℝ} (hκ : 0 < κ) (L τ : ℝ)
    (μ : Measure ((d → ℝ) × (Bool × ℝ))) [IsProbabilityMeasure μ] :
    (∫ z, |sampleStencilEstimate p T x₀ h ℓ r n κ hκ L z - τ|
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ z, |empiricalStencilEstimate p T x₀ h ℓ r
        (fun _ => Fin (balancedGroupSize (StencilRole d p) n)) κ hκ L z - τ|
        ∂Measure.pi (fun _ : Σ _ : StencilRole d p, Fin (balancedGroupSize (StencilRole d p) n) => μ) :=
  integral_balancedSample (StencilRole d p) μ n
    (by
      simpa only [Real.norm_eq_abs] using
        (((empiricalStencilEstimate_measurable p T x₀ h ℓ r _ hκ L).sub
          (measurable_const (a := τ))).norm).aestronglyMeasurable)

theorem sampleStencilEstimate_mae_le_sqrt_mse (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (n : ℕ) {κ L : ℝ} (hκ : 0 < κ) (hL : 0 ≤ L) (τ : ℝ)
    (μ : Measure ((d → ℝ) × (Bool × ℝ))) [IsProbabilityMeasure μ] :
    (∫ z, |sampleStencilEstimate p T x₀ h ℓ r n κ hκ L z - τ|
      ∂Measure.pi (fun _ : Fin n => μ)) ≤
      Real.sqrt (∫ z, (sampleStencilEstimate p T x₀ h ℓ r n κ hκ L z - τ) ^ 2
        ∂Measure.pi (fun _ : Fin n => μ)) := by
  rw [sampleStencilEstimate_mae_eq, sampleStencilEstimate_mse_eq]
  exact mean_absolute_le_sqrt_secondMoment _
    ((empiricalStencilEstimate_memLp p T x₀ h ℓ r _ hκ hL _).sub (memLp_const τ))

end CausalLowerbound.UpperBound

import CausalLowerbound.UniformLowerBound.GraphBounds
import CausalLowerbound.CommonMarginalTesting

/-! The fixed-cutoff component argument under the actual uniform covariate
law. The exceptional cluster event is paid once, and the good-event cost
is integrated using only two-coordinate marginals. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.UniformLowerBound
open PartB PartB.ShellGeometry
attribute [local instance] incidenceComponentFintype physicalComponentFintype
variable {d A : Type*} [Fintype d] [DecidableEq d] [Fintype A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

theorem good_collisionCost_integral_le (n Q : ℕ) (x₀ : d → ℝ)
    (ℓ h D : ℝ) (hℓ : 0 ≤ ℓ) (hh : 0 ≤ h) (hD : 0 ≤ D) :
    (∫ x, (largeClusterEvent n Q x₀ ℓ h)ᶜ.indicator
      (fun x => D * collisionCount x₀ ℓ h x) x ∂uniformDesign d n) ≤
      D * ((n : ℝ) ^ 2 * ((10 * h) ^ Fintype.card d * (8 * ℓ) ^ Fintype.card d)) := by
  have hi := (collisionCount_integrable x₀ ℓ h n).const_mul D
  calc
    _ ≤ ∫ x, D * collisionCount x₀ ℓ h x ∂uniformDesign d n := by
      apply integral_mono (hi.indicator (largeClusterEvent_measurable n Q x₀ ℓ h).compl) hi
      intro x
      by_cases hx : x ∈ (largeClusterEvent n Q x₀ ℓ h)ᶜ
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_not_mem hx]
        exact mul_nonneg hD (collisionCount_nonneg x₀ ℓ h x)
    _ = D * ∫ x, collisionCount x₀ ℓ h x ∂uniformDesign d n := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (collisionCount_integral_le x₀ ℓ h hℓ hh n) hD

theorem uniform_totalVariation_bound (n Q : ℕ) (x₀ : d → ℝ)
    (ℓ h D : ℝ) (hℓ : 0 ≤ ℓ) (hh : 0 ≤ h) (hD : 0 ≤ D)
    (P R : (Fin n → d → ℝ) → FiniteLaw A)
    (hP : ∀ a, Measurable (fun x => (P x).weight a))
    (hR : ∀ a, Measurable (fun x => (R x).weight a))
    (hlow : ∀ x, x ∉ largeClusterEvent n Q x₀ ℓ h →
      (P x).hellingerSq (R x) ≤ D * collisionCount x₀ ℓ h x) :
    (conditionalDensityLaw (uniformDesign d n) P hP).totalVariation
      (conditionalDensityLaw (uniformDesign d n) R hR) ≤
      clusterConstant d Q * ((n : ℝ) ^ (Q + 1) * h ^ Fintype.card d * ℓ ^ (Q * Fintype.card d)) +
        Real.sqrt (D * ((n : ℝ) ^ 2 *
          ((10 * h) ^ Fintype.card d * (8 * ℓ) ^ Fintype.card d))) := by
  exact (common_marginal_component_principle (uniformDesign d n) P R hP hR
    (largeClusterEvent n Q x₀ ℓ h) (largeClusterEvent_measurable n Q x₀ ℓ h)
    (fun x => D * collisionCount x₀ ℓ h x) ((collisionCount_integrable x₀ ℓ h n).const_mul D)
    hlow).trans
    (add_le_add (uniformDesign_largeCluster_real_probability_le n Q x₀ ℓ h hℓ hh)
      (Real.sqrt_le_sqrt (good_collisionCost_integral_le n Q x₀ ℓ h D hℓ hh hD)))

theorem uniform_component_two_point_lower_bound (n Q : ℕ) (x₀ : d → ℝ)
    (ℓ h D : ℝ) (hℓ : 0 ≤ ℓ) (hh : 0 ≤ h) (hD : 0 ≤ D)
    (P R : (Fin n → d → ℝ) → FiniteLaw A)
    (hP : ∀ a, Measurable (fun x => (P x).weight a))
    (hR : ∀ a, Measurable (fun x => (R x).weight a))
    (hlow : ∀ x, x ∉ largeClusterEvent n Q x₀ ℓ h →
      (P x).hellingerSq (R x) ≤ D * collisionCount x₀ ℓ h x)
    (hsmall : clusterConstant d Q *
      ((n : ℝ) ^ (Q + 1) * h ^ Fintype.card d * ℓ ^ (Q * Fintype.card d)) +
        Real.sqrt (D * ((n : ℝ) ^ 2 *
          ((10 * h) ^ Fintype.card d * (8 * ℓ) ^ Fintype.card d))) ≤ 1 / 2)
    (est : (Fin n → d → ℝ) × A → ℝ) (he : Measurable est)
    (θ₀ θ₁ : ℝ) (hθ : θ₀ ≤ θ₁) :
    ENNReal.ofReal ((θ₁ - θ₀) / 4) ≤
      max (∫⁻ z, ENNReal.ofReal |est z - θ₁| ∂conditionalExperiment (uniformDesign d n) P)
        (∫⁻ z, ENNReal.ofReal |est z - θ₀| ∂conditionalExperiment (uniformDesign d n) R) := by
  exact DensityLaw.two_point_quarter (conditionalDensityLaw (uniformDesign d n) P hP)
    (conditionalDensityLaw (uniformDesign d n) R hR) est he θ₀ θ₁ hθ
    ((uniform_totalVariation_bound n Q x₀ ℓ h D hℓ hh hD P R hP hR hlow).trans hsmall)

end CausalLowerbound.UniformLowerBound

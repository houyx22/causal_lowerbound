import CausalLowerbound.PartB.PhysicalFiniteExperiment
import CausalLowerbound.PartB.ObservationModels

/-! Measurability of the actual conditional experiments, including the
posterior induced by all countably many carrier labels. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped BigOperators Classical
namespace CausalLowerbound

theorem DiscreteLaw.expect_measurable {I X : Type*} [Countable I] [MeasurableSpace X]
    (μ : DiscreteLaw I) (f : I → X → ℝ) (B : ℝ)
    (hf : ∀ i, Measurable (f i)) (hb : ∀ i x, |f i x| ≤ B) :
    Measurable (fun x => μ.expect (fun i => f i x)) := by
  apply measurable_of_tendsto_metrizable' (atTop : Filter (Finset I))
    (fun s => Finset.measurable_sum s (fun i _ => measurable_const.mul (hf i)))
  exact tendsto_pi_nhds.mpr (fun x => (μ.summable_expect_of_bounded _ B (fun i => hb i x)).hasSum)

namespace PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω] [Inhabited Ω]

theorem sitesCarrierFactor_measurable (Q : ℕ) (θ : ℝ) (x₀ : d → ℝ) (r : ℝ)
    (n : ℕ) (k : d → ℤ) (label : ℕ) :
    Measurable (fun x : Fin n → d → ℝ => sitesCarrierFactor Q θ x₀ r x k label) :=
  Finset.measurable_prod _ (fun i _ => (physicalFactor_measurable Q θ label x₀ r k).comp (measurable_pi_apply i))

theorem physicalCoefficientPosteriors_measurable (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x₀ : d → ℝ) (r : ℝ) (n : ℕ) (k : S) (z : Ω) :
    Measurable (fun x : Fin n → d → ℝ => (physicalCoefficientPosteriors H kernel Q S θ hθ hθ1 x₀ r x k).weight z) := by
  have he (x : Fin n → d → ℝ) := posteriorLabelLaw_mixFinite H kernel Q θ hθ hθ1 x₀ r x k.val
  change Measurable (fun x : Fin n → d → ℝ =>
    (coefficientPosterior H kernel Q θ hθ hθ1 (fun i : carrierSites x₀ r k.val x =>
      torusProjection (carrierCoordinate (localCoordinate x₀ r k.val (x i.val))))).weight z)
  simp_rw [← he]
  change Measurable (fun x : Fin n → d → ℝ =>
    (H.tilt (sitesCarrierFactor Q θ x₀ r x k.val) ((1 - θ) ^ n) ((1 + θ) ^ n)
      (pow_pos (sub_pos.mpr hθ1) _) (sitesCarrierFactor_bounds Q θ hθ hθ1 x₀ r x k.val)).expect
        (fun label => (kernel label).weight z))
  simp_rw [DiscreteLaw.tilt_expect]
  have hb (label : ℕ) (x : Fin n → d → ℝ) : |sitesCarrierFactor Q θ x₀ r x k.val label| ≤ (1 + θ) ^ n := by
    rw [abs_of_nonneg ((pow_nonneg (sub_nonneg.mpr hθ1.le) n).trans
      (sitesCarrierFactor_bounds Q θ hθ hθ1 x₀ r x k.val label).1)]
    exact (sitesCarrierFactor_bounds Q θ hθ hθ1 x₀ r x k.val label).2
  apply (H.expect_measurable _ ((1 + θ) ^ n)
    (sitesCarrierFactor_measurable Q θ x₀ r n k.val) hb).inv.mul
  apply H.expect_measurable _ ((1 + θ) ^ n)
  · intro label
    exact (sitesCarrierFactor_measurable Q θ x₀ r n k.val label).mul_const _
  · intro label x
    rw [abs_mul, abs_of_nonneg ((kernel label).nonneg z)]
    exact (mul_le_of_le_one_right (abs_nonneg _) ((kernel label).weight_le_one z)).trans (hb label x)

theorem finitePhysicalConditional_measurable {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ) (n : ℕ)
    (μ : (Fin n → d → ℝ) → S → FiniteLaw Ω)
    (hμ : ∀ k z, Measurable (fun x => (μ x k).weight z))
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (w : Fin n → Bool × Bool) :
    Measurable (fun x => (finitePhysicalConditional side S atoms x₀ r h a b t δ (μ x) hlegal hκ x).weight w) := by
  change Measurable (fun x => ∑ z : S → Ω, (∏ k, (μ x k).weight (z k)) *
    ∏ i, ((modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).conditionalLaw
      (hlegal z) hκ (x i)).weight (w i))
  apply Finset.measurable_sum
  intro z _
  apply (Finset.measurable_prod _ (fun k _ => hμ k (z k))).mul
  apply Finset.measurable_prod
  intro i _
  exact ((NuisanceFields.conditionalLaw_measurable _ (hlegal z) hκ
    (modelFields_measurable side S _ x₀ r h a b t δ)) (w i)).comp (measurable_pi_apply i)

end PartB.ShellGeometry
end CausalLowerbound

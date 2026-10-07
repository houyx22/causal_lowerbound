import CausalLowerbound.PartB.DesignPosterior
import CausalLowerbound.PartB.CarrierPosteriorMoments
import CausalLowerbound.FiniteProductMixture

/-! Marginalizing the actual countable block-label posterior gives the
independent product of the finite coefficient posteriors at incident sites. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound

theorem DiscreteLaw.independent_mixFinite {K Ω : Type*} [Fintype K] [DecidableEq K] [Fintype Ω]
    (H : K → DiscreteLaw ℕ) (kernel : K → ℕ → FiniteLaw Ω) :
    (DiscreteLaw.independent H).mixFinite (fun labels => FiniteLaw.independent (fun k => kernel k (labels k))) =
      FiniteLaw.independent (fun k => (H k).mixFinite (kernel k)) := by
  apply FiniteLaw.ext
  intro x
  exact DiscreteLaw.expect_independent_prod H (fun k label => (kernel k label).weight (x k))
    (fun _ => 1) (fun k label => by
      rw [abs_of_nonneg ((kernel k label).nonneg (x k))]
      exact (kernel k label).weight_le_one (x k))

namespace PartB.ShellGeometry
open Wiener
variable {d K Ω : Type*} [Fintype d] [DecidableEq d] [Fintype K] [DecidableEq K] [Fintype Ω]

theorem varyingBlockPrior_coefficient_expect (H : K → DiscreteLaw ℕ)
    (kernel : K → ℕ → FiniteLaw Ω) (f : (K → Ω) → ℝ) :
    (varyingBlockPrior H kernel).expect (fun z => f z.2) =
      (FiniteLaw.independent (fun k => (H k).mixFinite (kernel k))).expect f := by
  have hb (x : K → Ω) : |f x| ≤ ∑ y, |f y| :=
    Finset.single_le_sum (fun y _ => abs_nonneg (f y)) (Finset.mem_univ x)
  unfold varyingBlockPrior
  rw [DiscreteLaw.expect_joint _ _ _ (∑ y, |f y|) (fun z => hb z.2)]
  change (DiscreteLaw.independent H).expect
    (fun labels => (FiniteLaw.independent (fun k => kernel k (labels k))).expect f) = _
  rw [← DiscreteLaw.mixFinite_expect, DiscreteLaw.independent_mixFinite]

def carrierSites (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) {n : ℕ}
    (x : Fin n → d → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ∈ carrierBox x₀ r k)

theorem sitesCarrierFactor_eq_densityTensor (Q : ℕ) (θ : ℝ) (x₀ : d → ℝ) (r : ℝ)
    {n : ℕ} (x : Fin n → d → ℝ) (k : d → ℤ) (label : ℕ) :
    sitesCarrierFactor Q θ x₀ r x k label =
      densityTensor Q θ label (fun i : carrierSites x₀ r k x =>
        torusProjection (carrierCoordinate (localCoordinate x₀ r k (x i.val)))) := by
  calc
    _ = ∏ i ∈ carrierSites x₀ r k x,
        labeledDensity Q θ label (torusProjection (carrierCoordinate (localCoordinate x₀ r k (x i)))) := by
      simp only [carrierSites, Finset.prod_filter, sitesCarrierFactor, physicalFactor]
    _ = _ := (Finset.prod_coe_sort _ _).symm

theorem posteriorLabelLaw_mixFinite (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r : ℝ)
    {n : ℕ} (x : Fin n → d → ℝ) (k : d → ℤ) :
    (posteriorLabelLaw H Q θ hθ hθ1 x₀ r x k).mixFinite kernel =
      coefficientPosterior H kernel Q θ hθ hθ1 (fun i : carrierSites x₀ r k x =>
        torusProjection (carrierCoordinate (localCoordinate x₀ r k (x i.val)))) := by
  unfold coefficientPosterior
  apply congrArg (fun ν : DiscreteLaw ℕ => ν.mixFinite kernel)
  apply DiscreteLaw.ext
  intro label
  change H.weight label * sitesCarrierFactor Q θ x₀ r x k label /
      H.expect (sitesCarrierFactor Q θ x₀ r x k) = _
  have he : sitesCarrierFactor Q θ x₀ r x k = fun label =>
      densityTensor Q θ label (fun i : carrierSites x₀ r k x =>
        torusProjection (carrierCoordinate (localCoordinate x₀ r k (x i.val)))) :=
    funext (sitesCarrierFactor_eq_densityTensor Q θ x₀ r x k)
  rw [he]
  rfl

theorem designPosterior_coefficient_expect (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x₀ : d → ℝ) (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) (f : (S → Ω) → ℝ) :
    (designPosterior H kernel Q S θ hθ hθ1 x₀ r x).expect (fun z => f z.2) =
      (FiniteLaw.independent (fun k : S => coefficientPosterior H kernel Q θ hθ hθ1
        (fun i : carrierSites x₀ r k.val x =>
          torusProjection (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))))).expect f := by
  rw [designPosterior, varyingBlockPrior_coefficient_expect]
  simp_rw [posteriorLabelLaw_mixFinite]

end PartB.ShellGeometry
end CausalLowerbound

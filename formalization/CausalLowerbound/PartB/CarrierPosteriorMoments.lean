import CausalLowerbound.DiscreteMixture
import CausalLowerbound.PartB.CarrierMasterIdentity
import CausalLowerbound.PartB.SmallDensityCarrier

/-! Actual finite coefficient posteriors under the full countable carrier,
and the exact Q-site posterior master moments. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped BigOperators
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d K Γ I : Type*} [Fintype d] [DecidableEq d] [Fintype K] [Fintype Γ] [Fintype I]

def coefficientPosterior (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Γ) (Q : ℕ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (u : K → Torus d) : FiniteLaw Γ :=
  (H.tilt (fun label => densityTensor Q θ label u)
    ((1 - θ) ^ Fintype.card K) ((1 + θ) ^ Fintype.card K)
    (pow_pos (sub_pos.mpr hθ1) _) (fun label => densityTensor_bounds Q θ hθ hθ1 label u)).mixFinite kernel

theorem coefficientPosterior_moment_difference (H : DiscreteLaw ℕ) (P Qk : ℕ → FiniteLaw Γ)
    (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (u : K → Torus d) (f : Γ → ℝ) :
    (coefficientPosterior H Qk Q θ hθ hθ1 u).expect f -
      (coefficientPosterior H P Q θ hθ hθ1 u).expect f =
        (densityMoment H Q θ u)⁻¹ * H.expect (fun label => densityTensor Q θ label u *
          ((Qk label).expect f - (P label).expect f)) := by
  exact H.posterior_moment_difference P Qk _ _ _ _ _ f

theorem positiveCarrier_posterior_moments (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (J : I → SymmetricReal d (Fin Q)) (feature : I → Γ → ℝ) (μ : FiniteLaw Γ)
    (hc : HasPositiveCarrier 1 (PositiveWiener.naturalAtom (d := d) (ι := Fin Q) θ)
      (multiplicationIncrement J) feature μ) :
    ∃ (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Γ),
      0 < H.weight 0 ∧ (∀ label x, 0 < (kernel label).weight x) ∧
      ∀ (u : Fin Q → Torus d) i,
        (coefficientPosterior H kernel Q θ hθ hθ1 u).expect (feature i) -
          (coefficientPosterior H (fun _ => μ) Q θ hθ hθ1 u).expect (feature i) =
            carrierEvaluation Q u (J i) := by
  obtain ⟨H, kernel, h0, hk, hm⟩ := hasPositiveCarrier_pointwise Q θ J feature μ hc
  refine ⟨H, kernel, h0, hk, ?_⟩
  intro u i
  rw [coefficientPosterior_moment_difference, hm u i,
    ← mul_assoc, inv_mul_cancel₀ (densityMoment_pos H Q θ hθ hθ1 u).ne', one_mul]

/-- All assumptions from the first two items have already been discharged:
the support, positive carrier, and posterior normalization are constructed. -/
theorem paper_posterior_master_moments (Q : ℕ) [NeZero Q] (ρ θ p B : ℝ)
    (hρ : 0 < ρ) (hθ : 0 < θ) (hθ1 : θ < 1) (hp : 0 < p)
    (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    ∀ᶠ n in atTop, ∃ (H : DiscreteLaw ℕ)
      (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))),
      0 < H.weight 0 ∧ (∀ label x, 0 < (kernel label).weight x) ∧
      ∀ (u : Fin Q → Torus d) η,
        (coefficientPosterior H kernel Q θ hθ.le hθ1 u).expect
          (monomialFeature (paperCoefficientAtoms Q ρ) η) -
        (coefficientPosterior H (fun _ => paperCoefficientLaw Q) Q θ hθ.le hθ1 u).expect
          (monomialFeature (paperCoefficientAtoms Q ρ) η) =
        carrierEvaluation Q u (paperIdealVector Q (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ) p B n η) := by
  filter_upwards [paper_positiveCarrier_contrast (d := d) Q ρ θ hρ hθ p B hp hB] with n hn
  exact positiveCarrier_posterior_moments Q θ hθ.le hθ1 _ _ _ hn

end CausalLowerbound.PartB.ShellGeometry

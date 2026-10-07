import CausalLowerbound.PartC.PhysicalPropensityProjectivity
import CausalLowerbound.PartC.DensityCarrierPosterior

/-! The physical propensity carrier's finite coefficient posterior and
its retained-site likelihood increment. The normalizer is the actual
retained design marginal, which is strictly positive. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial RoughPropensity
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G Ω : Type*} [Fintype d] [DecidableEq d]
  [Fintype I] [Fintype G] [Fintype Ω]
variable {Q : ℕ} {ρ : ℝ} {x₀ : d → ℝ} {ℓ r h : ℝ} {k : d → ℤ}
  {c w N N₀ θ ja t τ K δ : ℝ}

namespace HasPaperPropensityCarrier
variable (hcarr : HasPaperPropensityCarrier Q ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ)

def posterior (hθ1 : θ < 1) (H : DiscreteLaw ℕ)
    (kernel : (activeBlocks (d := d) ℓ h → Bool) → ℕ → FiniteLaw Ω)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : I → d → ℝ) : FiniteLaw Ω :=
  densityCarrierPosterior H
    (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) (kernel ζ)
    (1 - θ) (1 + θ) (sub_pos.mpr hθ1) (fun n x => hcarr.2.2.1 n ζ x) u

include hcarr in
theorem marginal_pos (hθ1 : θ < 1) (H : DiscreteLaw ℕ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : I → d → ℝ) :
    0 < carrierMarginal H
      (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) u :=
  carrierMarginal_pos H _ (1 - θ) (1 + θ) (sub_pos.mpr hθ1) (fun n x => hcarr.2.2.1 n ζ x) u

theorem posterior_increment (hθ1 : θ < 1) (H : DiscreteLaw ℕ)
    (kernel : (activeBlocks (d := d) ℓ h → Bool) → ℕ → FiniteLaw Ω)
    (μ : FiniteLaw Ω) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : I → d → ℝ) (f : Ω → ℝ) :
    (hcarr.posterior hθ1 H kernel ζ u).expect f - μ.expect f =
      (carrierMarginal H
        (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) u)⁻¹ *
        weightedCarrierMarginal H
          (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ)
          (fun n => (kernel ζ n).expect f - μ.expect f) u :=
  densityCarrierPosterior_increment H _ (kernel ζ) μ (1 - θ) (1 + θ) (sub_pos.mpr hθ1)
    (fun n x => hcarr.2.2.1 n ζ x) u f

theorem likelihood_increment_of_projection (hθ1 : θ < 1) (H : DiscreteLaw ℕ)
    (kernel : (activeBlocks (d := d) ℓ h → Bool) → ℕ →
      FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (B : Representative.Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (hproject : ∀ p : MvPolynomial (CoefficientExponent d Q) ℝ, p.totalDegree ≤ 4 * Q →
      weightedCarrierMarginal H
        (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ)
        (fun n => (kernel ζ n).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p) -
          (paperCoefficientLaw Q).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p)) u =
        ∫ z : G → d → ℝ,
          physicalPropensityIncrementValue Q ρ x₀ ℓ r h k c w N ja t τ B ζ p (completedConfiguration e u z)
            ∂Measure.pi (fun _ : G => cubeMeasure d))
    (R T siteJa rough offset ψ : I → ℝ) :
    (hcarr.posterior hθ1 H kernel ζ u).expect (fun ω => ∏ i,
      likelihood (R i) (T i) (siteJa i) (offset i + ψ i * coefficientEvaluation (paperCoefficientAtoms Q ρ ω) (u i))
        (rough i)) -
      (paperCoefficientLaw Q).expect (fun ω => ∏ i,
        likelihood (R i) (T i) (siteJa i) (offset i + ψ i * coefficientEvaluation (paperCoefficientAtoms Q ρ ω) (u i))
          (rough i)) =
      (carrierMarginal H
        (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) u)⁻¹ *
        ∫ z : G → d → ℝ,
          physicalPropensityIncrementValue Q ρ x₀ ℓ r h k c w N ja t τ B ζ
            (retainedPropensityPolynomial Q R T siteJa rough offset ψ u) (completedConfiguration e u z)
              ∂Measure.pi (fun _ : G => cubeMeasure d) := by
  have hcard : Fintype.card I + Fintype.card G = Q := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr e
  have hp : (retainedPropensityPolynomial Q R T siteJa rough offset ψ u).totalDegree ≤ 4 * Q :=
    (retainedPropensityPolynomial_degree Q R T siteJa rough offset ψ u).trans (by omega)
  rw [hcarr.posterior_increment]
  apply congrArg (fun a : ℝ => (carrierMarginal H
    (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) u)⁻¹ * a)
  simpa only [retainedPropensityPolynomial_eval] using hproject _ hp

end HasPaperPropensityCarrier
end CausalLowerbound.PartC

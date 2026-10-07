import CausalLowerbound.PartC.PropensityMomentWitness
import CausalLowerbound.PartC.GhostPatternProjection

/-! Identify the empty ghost pattern with the design marginal of the
same constructed carrier law. No replacement carrier or projection
hypothesis is needed when forming the reference mixture. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype G]

theorem physicalPropensityFullFunctional_C
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N ja t τ : ℝ)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : Fin Q × d → ℝ) (a : ℝ) :
    physicalPropensityFullFunctional Q ρ x₀ ℓ r h k c w N ja t τ B ζ u (C a) =
      a * physicalCarrierValue x₀ ℓ r h k c w N B ζ u := by
  simp only [physicalPropensityFullFunctional_apply, eval_C, FiniteLaw.expect_const,
    physicalPropensityIncrementValue, paperPhysicalPropensityPolynomial_C, add_zero]

namespace PropensityMomentWitness
variable {Q : ℕ} {ρ : ℝ} {x₀ : d → ℝ} {ℓ r h : ℝ} {k : d → ℤ}
  {c w N N₀ θ ja t τ K δ : ℝ}
variable (R : PropensityMomentWitness Q ρ x₀ ℓ r h k c w N θ ja t τ)

theorem carrier_projective
    (hcarr : HasPaperPropensityCarrier Q ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ) (hθ : 0 ≤ θ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) :
    carrierMarginal R.law
      (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) u =
      ∫ z : G → d → ℝ, physicalCarrierValue x₀ ℓ r h k c w N R.representative ζ
        (completedConfiguration e u z) ∂Measure.pi (fun _ : G => cubeMeasure d) := by
  have he := R.weighted_projective hcarr hθ ζ e u hu (C 1) (by simp)
  simpa only [weightedCarrierMarginal, carrierMarginal, eval_C, FiniteLaw.expect_const,
    mul_one, physicalPropensityFullFunctional_C, one_mul] using he

theorem empty_ghost_eq_carrierMarginal
    (hcarr : HasPaperPropensityCarrier Q ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ) (hθ : 0 ≤ θ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) :
    physicalGhostPatternWeight Q x₀ ℓ r h k c w N ja τ R.representative e u ζ ζ ∅ =
      carrierMarginal R.law
        (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) u := by
  rw [R.carrier_projective hcarr hθ ζ e u hu]
  have he := physicalGhostPatternWeight_eq_integral Q x₀ ℓ r h k c w N ja τ R.representative e u ζ ∅
  simpa only [Finset.card_empty, pow_zero, one_mul, taperedPatternWeight, if_pos rfl,
    if_true, propensityPatternWeight_empty, physicalCarrierValue, configurationSite] using he

theorem untapered_empty_ghost_eq_carrierMarginal
    (hcarr : HasPaperPropensityCarrier Q ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ) (hθ : 0 ≤ θ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) :
    ghostPatternIntegral x₀ ℓ r h k c w N ja R.representative e u
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i)) ζ ∅ (fun _ => 1) =
      carrierMarginal R.law
        (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) u := by
  exact R.empty_ghost_eq_carrierMarginal hcarr hθ ζ e u hu

end PropensityMomentWitness
end CausalLowerbound.PartC

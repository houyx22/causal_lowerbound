import CausalLowerbound.PartC.OutcomeMomentWitness
import CausalLowerbound.PartC.PhysicalOutcomePatternIntegrands

/-! The zero cubic pattern is the design marginal of the same outcome
carrier law. Its constant moment keeps the actual baseline unchanged. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype G]

theorem physicalOutcomeFullFunctional_C
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N t τ : ℝ)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : Fin Q × d → ℝ) (a : ℝ) :
    physicalOutcomeFullFunctional Q ρ x₀ ℓ r h k c w N t τ B ζ u (C a) =
      a * physicalCarrierValue x₀ ℓ r h k c w N B ζ u := by
  simp only [physicalOutcomeFullFunctional_apply, eval_C, FiniteLaw.expect_const,
    paperPhysicalOutcomePolynomial_C, add_zero]

namespace OutcomeMomentWitness
variable {Q : ℕ} {ρ : ℝ} {x₀ : d → ℝ} {ℓ r h : ℝ} {k : d → ℤ}
  {c w N N₀ θ t τ K δ : ℝ}
variable (R : OutcomeMomentWitness Q ρ x₀ ℓ r h k c w N θ t τ)

theorem carrier_projective
    (hcarr : HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k c w N N₀ θ t τ K δ) (hθ : 0 ≤ θ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) :
    carrierMarginal R.law
      (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ) u =
      ∫ z : G → d → ℝ, physicalCarrierValue x₀ ℓ r h k c w N R.representative ζ
        (completedConfiguration e u z) ∂Measure.pi (fun _ : G => cubeMeasure d) := by
  have he := R.weighted_projective hcarr hθ ζ e u hu (C 1) (by simp)
  simpa only [weightedCarrierMarginal, carrierMarginal, eval_C, FiniteLaw.expect_const,
    mul_one, physicalOutcomeFullFunctional_C, one_mul] using he

theorem zero_ghost_eq_carrierMarginal
    (hcarr : HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k c w N N₀ θ t τ K δ) (hθ : 0 ≤ θ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) :
    physicalGhostOutcomePatternWeight Q x₀ ℓ r h k c w N τ R.representative e u ζ ζ 0 =
      carrierMarginal R.law
        (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ) u := by
  rw [R.carrier_projective hcarr hθ ζ e u hu]
  unfold physicalGhostOutcomePatternWeight ghostOutcomePatternIntegral
  apply integral_congr_ae
  filter_upwards [] with g
  rw [partialPhysicalOutcomePatternWeight_diagonal]
  simp only [selectedOutcomeGhostTaper, if_pos rfl, if_true, one_mul, weightedOutcomePatternWeight,
    degreeSize, Pi.zero_apply, Pi.zero_def, Fin.val_zero, Finset.sum_const_zero, pow_zero, one_mul,
    outcomePatternWeight_zero]
  rfl

theorem untapered_zero_ghost_eq_carrierMarginal
    (hcarr : HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k c w N N₀ θ t τ K δ) (hθ : 0 ≤ θ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) :
    ghostOutcomePatternIntegral x₀ ℓ r h k c w N R.representative e u
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i)) ζ 0 (fun _ => 1) =
      carrierMarginal R.law
        (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ) u := by
  have hzero : selectedOutcomeGhostTaper Q e τ u (0 : Degree (Fin Q) 3) =
      (fun _ : G → d → ℝ => (1 : ℝ)) := by
    funext g
    simp only [selectedOutcomeGhostTaper, if_pos rfl, if_true]
  simpa only [physicalGhostOutcomePatternWeight, hzero] using
    R.zero_ghost_eq_carrierMarginal hcarr hθ ζ e u hu

end OutcomeMomentWitness
end CausalLowerbound.PartC

import CausalLowerbound.PartC.DensityCarrierMarginals
import CausalLowerbound.PartC.UnitCubeGhosts
import CausalLowerbound.PartC.PhysicalPropensityLikelihood

/-! Ghost projectivity for the actual physical density dictionary.
The rough signs are fixed throughout the projection; the coefficient
weight may depend on those signs but never on the ghost coordinates. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G Ω : Type*} [Fintype d] [DecidableEq d]
  [Fintype I] [Fintype G] [Fintype Ω]
variable {Q : ℕ} {ρ : ℝ} {x₀ : d → ℝ} {ℓ r h : ℝ} {k : d → ℤ}
  {c w N N₀ θ ja t τ K δ : ℝ}

namespace HasPaperPropensityCarrier
variable (hcarr : HasPaperPropensityCarrier Q ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ)
include hcarr

theorem density_abs_le (n : ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) (u : d → ℝ) :
    |carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ u| ≤ 1 + θ := by
  obtain ⟨hlo, hhi⟩ := hcarr.2.2.1 n ζ u
  exact abs_le.mpr ⟨by linarith, hhi⟩

theorem weighted_projective (hθ : 0 ≤ θ) (H : DiscreteLaw ℕ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (g : ℕ → ℝ) (M : ℝ) (hg : ∀ n, |g n| ≤ M)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ) :
    (∫ z : G → d → ℝ, weightedCarrierMarginal H
      (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ)
      g (completedSites e u z) ∂Measure.pi (fun _ : G => cubeMeasure d)) =
      weightedCarrierMarginal H
        (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) g u := by
  exact weightedCarrierMarginal_completed (cubeMeasure d) H _ g (1 + θ) M (by linarith)
    (fun n => hcarr.1 n ζ) (fun n x => hcarr.density_abs_le n ζ x)
    (fun n => hcarr.2.1 n ζ) hg e u

theorem coefficient_difference_projective (hθ : 0 ≤ θ) (H : DiscreteLaw ℕ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (kernel : ℕ → FiniteLaw Ω) (μ : FiniteLaw Ω)
    (f : Ω → ℝ) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ) :
    (∫ z : G → d → ℝ, weightedCarrierMarginal H
      (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ)
      (fun n => (kernel n).expect f - μ.expect f) (completedSites e u z)
        ∂Measure.pi (fun _ : G => cubeMeasure d)) =
      weightedCarrierMarginal H
        (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ)
        (fun n => (kernel n).expect f - μ.expect f) u :=
  hcarr.weighted_projective hθ H ζ _ (2 * ∑ y, |f y|)
    (coefficient_difference_bound kernel μ f) e u

/-- A full-chart identity for a fixed bounded label weight can be
integrated in the ghosts without changing that weight or the law. -/
theorem projective_hasSum (hθ : 0 ≤ θ) (H : DiscreteLaw ℕ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (g : ℕ → ℝ) (M : ℝ) (hg : ∀ n, |g n| ≤ M)
    (F : (Fin Q × d → ℝ) → ℝ)
    (hsum : ∀ v : UnitChart (Fin Q × d), HasSum (fun n => (H.weight n * g n) *
      ∏ j, carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ (fun a => v.val (j, a)))
      (F v.val)) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) :
    weightedCarrierMarginal H
      (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) g u =
      ∫ z : G → d → ℝ, F (completedConfiguration e u z) ∂Measure.pi (fun _ : G => cubeMeasure d) := by
  rw [← hcarr.weighted_projective hθ H ζ g M hg e u]
  apply integral_congr_ae
  filter_upwards [ae_completedConfiguration_mem_Icc e u hu] with z hz
  exact weightedCarrierMarginal_eq_of_hasSum H _ g (completedSites e u z) _
    (hsum ⟨completedConfiguration e u z, hz⟩)

end HasPaperPropensityCarrier
end CausalLowerbound.PartC

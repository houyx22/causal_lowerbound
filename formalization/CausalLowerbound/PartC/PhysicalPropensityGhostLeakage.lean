import CausalLowerbound.PartC.PhysicalPropensityPosterior
import CausalLowerbound.PartC.DensityGhostLeakage
import CausalLowerbound.PartC.CompletedCubeTaper

/-! Quantitative ghost error for the actual sign-dependent physical
propensity density. The normalized error lies in [0,1]; its integral
against the retained design marginal has the concrete tau^s bound. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype G]

def physicalCarrierGhostError (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N θ : ℝ) (H : DiscreteLaw ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (e : I ⊕ G ≃ Fin Q) (τ : ℝ) (u : I → d → ℝ) : ℝ :=
  carrierGhostDefect (cubeMeasure d) H
    (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ)
    (completedCubeTaper Q e τ) u /
    carrierMarginal H
      (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) u

namespace HasPaperPropensityCarrier
variable {Q : ℕ} {ρ : ℝ} {x₀ : d → ℝ} {ℓ r h : ℝ} {k : d → ℤ}
  {c w N N₀ θ ja t τ K δ : ℝ}
variable (hcarr : HasPaperPropensityCarrier Q ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ)
include hcarr

theorem ghostError_bounds (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ) :
    0 ≤ physicalCarrierGhostError Q x₀ ℓ r h k c w N θ H ζ e τ u ∧
      physicalCarrierGhostError Q x₀ ℓ r h k c w N θ H ζ e τ u ≤ 1 := by
  have hd := hcarr.marginal_pos hθ1 H ζ u
  unfold physicalCarrierGhostError
  constructor
  · exact div_nonneg (carrierGhostDefect_nonneg (cubeMeasure d) H _ (1 - θ) (1 + θ)
      (sub_nonneg.mpr hθ1.le) (fun n x => hcarr.2.2.1 n ζ x) _
      (fun v => (completedCubeTaper_bounds Q e τ v).2) u) hd.le
  · apply (div_le_one hd).mpr
    exact carrierGhostDefect_le_marginal (cubeMeasure d) H _ (1 - θ) (1 + θ)
      (sub_nonneg.mpr hθ1.le) (by linarith) (fun n => hcarr.1 n ζ)
      (fun n x => hcarr.2.2.1 n ζ x) (fun n => hcarr.2.1 n ζ)
      _ (completedCubeTaper_continuous Q e τ) (completedCubeTaper_bounds Q e τ) u

theorem ghostError_weighted (hθ1 : θ < 1) (H : DiscreteLaw ℕ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ) :
    carrierMarginal H
      (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ) u *
      physicalCarrierGhostError Q x₀ ℓ r h k c w N θ H ζ e τ u =
      carrierGhostDefect (cubeMeasure d) H
        (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ)
        (completedCubeTaper Q e τ) u := by
  unfold physicalCarrierGhostError
  field_simp [(hcarr.marginal_pos hθ1 H ζ u).ne']

theorem ghostDefect_integrable (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : I ⊕ G ≃ Fin Q) :
    Integrable (carrierGhostDefect (cubeMeasure d) H
      (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ)
      (completedCubeTaper Q e τ)) (Measure.pi (fun _ : I => cubeMeasure d)) :=
  carrierGhostDefect_integrable (cubeMeasure d) H _ (1 - θ) (1 + θ)
    (sub_nonneg.mpr hθ1.le) (by linarith) (fun n => hcarr.1 n ζ) (fun n x => hcarr.2.2.1 n ζ x)
    _ (completedCubeTaper_continuous Q e τ) (completedCubeTaper_bounds Q e τ)

theorem ghostError_integrable (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (e : I ⊕ G ≃ Fin Q) :
    Integrable (physicalCarrierGhostError Q x₀ ℓ r h k c w N θ H ζ e τ)
      (Measure.pi (fun _ : I => cubeMeasure d)) := by
  have hi := hcarr.ghostDefect_integrable hθ hθ1 H ζ e
  have hd : Continuous (carrierMarginal (I := I) H
      (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ n ζ)) := by
    exact H.expect_continuous _ ((1 + θ) ^ Fintype.card I)
      (fun n => carrierTensor_continuous _ (fun n => hcarr.1 n ζ) n)
      (fun n u => carrierTensor_abs_le _ (1 + θ) (fun n x => hcarr.density_abs_le n ζ x) n u)
  have hm : AEStronglyMeasurable (physicalCarrierGhostError Q x₀ ℓ r h k c w N θ H ζ e τ)
      (Measure.pi (fun _ : I => cubeMeasure d)) :=
    (hi.aestronglyMeasurable.aemeasurable.div hd.measurable.aemeasurable).aestronglyMeasurable
  apply (integrable_const (1 : ℝ)).mono' hm
  apply Filter.Eventually.of_forall
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (hcarr.ghostError_bounds hθ hθ1 H ζ e u).1]
  exact (hcarr.ghostError_bounds hθ hθ1 H ζ e u).2

end HasPaperPropensityCarrier

theorem HasPaperPropensityCarrier.concrete_weighted_ghost_bound [Nonempty d]
    (q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N N₀ θ ja t τ K δ : ℝ)
    (hcarr : HasPaperPropensityCarrier (q + 1) ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (e : I ⊕ G ≃ Fin (q + 1)) (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (hτ : 0 < τ) :
    (∫ u : I → d → ℝ,
      carrierMarginal H
        (fun n => carrierPhysicalDensity (ι := Fin (q + 1)) (D := 1) x₀ ℓ r h k c w N θ n ζ) u *
        physicalCarrierGhostError (q + 1) x₀ ℓ r h k c w N θ H ζ e τ u
          ∂Measure.pi (fun _ : I => cubeMeasure d)) ≤
      (1 + θ) ^ (q + 1) * ((q + 1 : ℝ) * ((2 * τ) ^ s * collisionMomentBound d s ^ q)) := by
  simp_rw [hcarr.ghostError_weighted hθ1 H ζ e]
  have hv := carrierGhostDefect_volume_bound (cubeMeasure d) H
    (fun n => carrierPhysicalDensity (ι := Fin (q + 1)) (D := 1) x₀ ℓ r h k c w N θ n ζ)
    (1 - θ) (1 + θ) (sub_nonneg.mpr hθ1.le) (by linarith)
    (fun n => hcarr.1 n ζ) (fun n x => hcarr.2.2.1 n ζ x)
    (completedCubeTaper (q + 1) e τ) (completedCubeTaper_continuous (q + 1) e τ)
    (completedCubeTaper_bounds (q + 1) e τ)
  have hcard : Fintype.card (I ⊕ G) = q + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  rw [hcard] at hv
  exact hv.trans (mul_le_mul_of_nonneg_left (completedCubeTaper_bad_volume q e s hs hsd τ hτ)
    (pow_nonneg (by linarith) _))

theorem HasPaperPropensityCarrier.concrete_ghost_bound [Nonempty d]
    (q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N N₀ θ ja t τ K δ : ℝ)
    (hcarr : HasPaperPropensityCarrier (q + 1) ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (e : I ⊕ G ≃ Fin (q + 1)) (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (hτ : 0 < τ) :
    (∫ u : I → d → ℝ, physicalCarrierGhostError (q + 1) x₀ ℓ r h k c w N θ H ζ e τ u
      ∂Measure.pi (fun _ : I => cubeMeasure d)) ≤
      ((1 + θ) ^ (q + 1) * ((q + 1 : ℝ) * ((2 * τ) ^ s * collisionMomentBound d s ^ q))) /
        (1 - θ) ^ Fintype.card I := by
  have hi := hcarr.ghostError_integrable hθ hθ1 H ζ e
  have hwi := (hcarr.ghostDefect_integrable hθ hθ1 H ζ e).congr
    (Filter.Eventually.of_forall (fun u => (hcarr.ghostError_weighted hθ1 H ζ e u).symm))
  apply (le_div_iff₀ (pow_pos (sub_pos.mpr hθ1) _)).mpr
  rw [mul_comm, ← integral_const_mul]
  apply (integral_mono (hi.const_mul _) hwi (fun u => mul_le_mul_of_nonneg_right
    (carrierMarginal_bounds H _ (1 - θ) (1 + θ) (sub_nonneg.mpr hθ1.le)
      (fun n x => hcarr.2.2.1 n ζ x) u).1 (hcarr.ghostError_bounds hθ hθ1 H ζ e u).1)).trans
  exact hcarr.concrete_weighted_ghost_bound q ρ x₀ ℓ r h k c w N N₀ θ ja t τ K δ hθ hθ1 H ζ e s hs hsd hτ

end CausalLowerbound.PartC

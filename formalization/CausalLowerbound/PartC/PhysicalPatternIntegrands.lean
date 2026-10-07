import CausalLowerbound.PartC.GhostPatternProjection

/-! The actual integrand of the ghost pattern weights. Its diagonal form
is exactly the normalized tapered weight in the observation expansion;
continuity and a uniform bound justify subsequent finite-sum exchanges. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype G]

def physicalGhostPatternIntegrand (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N ja τ : ℝ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (S : Finset (Fin Q)) (g : G → d → ℝ) : ℝ :=
  selectedGhostTaper Q e τ u S g * partialPhysicalPatternWeight x₀ ℓ r h k c w N ja B e u
    (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i)) η S g

theorem physicalGhostPatternIntegrand_diagonal (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N ja τ : ℝ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (S : Finset (Fin Q)) (g : G → d → ℝ) :
    physicalGhostPatternIntegrand Q x₀ ℓ r h k c w N ja τ B e u ζ ζ S g =
      (if S = ∅ then 1 else completeTaper Q τ (completedConfiguration e u g)) *
        weightedPropensityPatternWeight N
          (physicalPropensitySlotCorrection x₀ r h k c w N ja (completedConfiguration e u g))
          B (completedConfiguration e u g)
          (fun v => normalizedRoughChart x₀ ℓ r h k c w N ζ
            (configurationSite (completedConfiguration e u g) v)) ζ S := by
  have hz : completedSites e (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i))
      (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (g j)) =
      fun v => normalizedRoughChart x₀ ℓ r h k c w N ζ
        (configurationSite (completedConfiguration e u g) v) := by
    funext v
    change completedSites e (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i))
      (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (g j)) v =
        normalizedRoughChart x₀ ℓ r h k c w N ζ (completedSites e u g v)
    cases hv : e.symm v <;> simp only [completedSites, Function.comp_apply, hv,
      Sum.elim_inl, Sum.elim_inr]
  simp only [physicalGhostPatternIntegrand, partialPhysicalPatternWeight, hz,
    selectedGhostTaper, completedCubeTaper]

theorem physicalGhostPatternIntegrand_integrable
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N N₀ ja τ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hja : ja ^ 2 ≤ 1)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (S : Finset (Fin Q)) :
    Integrable (physicalGhostPatternIntegrand Q x₀ ℓ r h k c w N ja τ B e u ζ η S)
      (Measure.pi (fun _ : G => cubeMeasure d)) := by
  let C := 1 + N₀ / c + 1 / (c * N₀)
  have hcz : 0 ≤ N₀ / c := by positivity
  have hcκ : 0 ≤ 1 / (c * N₀) := by positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCz : N₀ / c ≤ C := by dsimp [C]; linarith
  have hCκ : 1 / (c * N₀) ≤ C := by dsimp [C]; linarith
  apply (integrable_const (C ^ Q * ‖B‖)).mono'
  · exact ((selectedGhostTaper_continuous Q e τ u S).mul
      (partialPhysicalPatternWeight_continuous x₀ ℓ r h k c w N ja hc B e u
        (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i)) η S)).aestronglyMeasurable
  · filter_upwards [] with g
    change |physicalGhostPatternIntegrand Q x₀ ℓ r h k c w N ja τ B e u ζ η S g| ≤ C ^ Q * ‖B‖
    rw [physicalGhostPatternIntegrand, abs_mul]
    calc
      _ ≤ 1 * |partialPhysicalPatternWeight x₀ ℓ r h k c w N ja B e u
        (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i)) η S g| :=
          mul_le_mul_of_nonneg_right (selectedGhostTaper_abs_le Q e τ u S g) (abs_nonneg _)
      _ ≤ _ := by
        simpa only [one_mul, Fintype.card_fin] using
          partialPhysicalPatternWeight_bound x₀ ℓ r h k c w N N₀ ja hc hN₀ hN hm hrough hja B e u
            (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i))
            (fun i => normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i))
            C hC hCz hCκ (fun i =>
              (normalizedRoughChart_scaled_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i)).trans hCz)
            η S g

end CausalLowerbound.PartC

import CausalLowerbound.PartC.PhysicalGhostOutcomePatterns
import CausalLowerbound.PartC.GhostTaperRemoval

/-! Removing the actual graph taper in a cubic ghost pattern costs its
geometric defect integral. The pattern bound has no growth in N. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype G]

theorem selectedOutcomeGhostTaper_defect_integrable (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ)
    (u : I → d → ℝ) (D : Degree (Fin Q) 3) :
    Integrable (fun g => 1 - selectedOutcomeGhostTaper Q e τ u D g)
      (Measure.pi (fun _ : G => cubeMeasure d)) :=
  continuous_integrable_cubeSites _
    (continuous_const.sub (selectedOutcomeGhostTaper_continuous Q e τ u D))

theorem selectedOutcomeGhostTaper_defect_le (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ)
    (u : I → d → ℝ) (D : Degree (Fin Q) 3) :
    (∫ g, 1 - selectedOutcomeGhostTaper Q e τ u D g ∂Measure.pi (fun _ : G => cubeMeasure d)) ≤
      completedGhostTaperDefect Q e τ u := by
  by_cases hD : D = 0
  · simpa only [selectedOutcomeGhostTaper, if_pos hD, sub_self, integral_zero] using
      (completedGhostTaperDefect_bounds Q e τ u).1
  · simp only [selectedOutcomeGhostTaper, if_neg hD, completedGhostTaperDefect, le_refl]

theorem physicalGhostOutcomePatternWeight_taper_removal_bound
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N N₀ τ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (D : Degree (Fin Q) 3) :
    |physicalGhostOutcomePatternWeight Q x₀ ℓ r h k c w N τ B e u ζ η D -
      ghostOutcomePatternIntegral x₀ ℓ r h k c w N B e u
        (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i)) η D (fun _ => 1)| ≤
      (((1 + N₀ / c + 1 / N₀ ^ 2) ^ 4) ^ Q * ‖B‖) * completedGhostTaperDefect Q e τ u := by
  let μ := Measure.pi (fun _ : G => cubeMeasure d)
  let F := partialPhysicalOutcomePatternWeight x₀ ℓ r h k c w N B e u
    (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i)) η D
  let χ := selectedOutcomeGhostTaper Q e τ u D
  let C := 1 + N₀ / c + 1 / N₀ ^ 2
  let M := (C ^ 4) ^ Q * ‖B‖
  have hcz : 0 ≤ N₀ / c := by positivity
  have hcκ : 0 ≤ 1 / N₀ ^ 2 := by positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCz : N₀ / c ≤ C := by dsimp [C]; linarith
  have hCκ : 1 / N₀ ^ 2 ≤ C := by dsimp [C]; linarith
  have hM : 0 ≤ M := mul_nonneg (pow_nonneg (pow_nonneg (zero_le_one.trans hC) 4) Q) (norm_nonneg _)
  have hF (g : G → d → ℝ) : |F g| ≤ M := by
    simpa only [Fintype.card_fin] using partialPhysicalOutcomePatternWeight_bound x₀ ℓ r h k c w N N₀
      hc hN₀ hN hm hrough B e u _
      (fun i => normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i))
      C hC hCz hCκ (fun i =>
        (normalizedRoughChart_scaled_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i)).trans hCz)
      η D g
  have hi : Integrable F μ := partialPhysicalOutcomePatternWeight_integrable x₀ ℓ r h k c w N hc B e u _ η D
  change |(∫ g, χ g * F g ∂μ) - ∫ g, (1 : ℝ) * F g ∂μ| ≤ _
  simp only [one_mul]
  apply (integral_taper_removal_bound μ F χ M hM hi
    (selectedOutcomeGhostTaper_continuous Q e τ u D).aestronglyMeasurable hF
    (selectedOutcomeGhostTaper_abs_le Q e τ u D)).trans
  exact mul_le_mul_of_nonneg_left (selectedOutcomeGhostTaper_defect_le Q e τ u D) hM

end CausalLowerbound.PartC

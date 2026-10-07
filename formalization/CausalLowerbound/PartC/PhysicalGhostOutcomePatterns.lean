import CausalLowerbound.PartC.GhostOutcomePatternParity
import CausalLowerbound.PartC.CompletedCubeTaper

/-! Cubic ghost patterns with actual retained rough values and the
complete-graph taper. The zero-degree pattern keeps its baseline weight. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype G]

def selectedOutcomeGhostTaper (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ)
    (u : I → d → ℝ) (D : Degree (Fin Q) 3) (g : G → d → ℝ) : ℝ :=
  if D = 0 then 1 else completedCubeTaper Q e τ (u, g)

theorem selectedOutcomeGhostTaper_continuous (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ)
    (u : I → d → ℝ) (D : Degree (Fin Q) 3) :
    Continuous (selectedOutcomeGhostTaper Q e τ u D) := by
  change Continuous (fun g : G → d → ℝ => if D = 0 then (1 : ℝ) else completedCubeTaper Q e τ (u, g))
  by_cases hD : D = 0
  · simpa only [if_pos hD] using
      (continuous_const : Continuous (fun _ : G → d → ℝ => (1 : ℝ)))
  · simp only [if_neg hD]
    exact (completedCubeTaper_continuous Q e τ).comp
      ((continuous_const : Continuous (fun _ : G → d → ℝ => u)).prodMk continuous_id)

theorem selectedOutcomeGhostTaper_abs_le (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ)
    (u : I → d → ℝ) (D : Degree (Fin Q) 3) (g : G → d → ℝ) :
    |selectedOutcomeGhostTaper Q e τ u D g| ≤ 1 := by
  by_cases hD : D = 0
  · simp only [selectedOutcomeGhostTaper, if_pos hD, abs_one, le_refl]
  · rw [selectedOutcomeGhostTaper, if_neg hD, abs_of_nonneg (completedCubeTaper_bounds Q e τ (u, g)).1]
    exact (completedCubeTaper_bounds Q e τ (u, g)).2

def physicalGhostOutcomePatternWeight (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N τ : ℝ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (D : Degree (Fin Q) 3) : ℝ :=
  ghostOutcomePatternIntegral x₀ ℓ r h k c w N B e u
    (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i)) η D (selectedOutcomeGhostTaper Q e τ u D)

theorem physicalGhostOutcomePatternWeight_parity (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N τ : ℝ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (hB : reflection B = B) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (D : Degree (Fin Q) 3) :
    physicalGhostOutcomePatternWeight Q x₀ ℓ r h k c w N τ B e u (Walsh.flip ζ) (Walsh.flip η) D =
      (-1) ^ degreeSize D * physicalGhostOutcomePatternWeight Q x₀ ℓ r h k c w N τ B e u ζ η D := by
  unfold physicalGhostOutcomePatternWeight
  exact ghostOutcomePatternIntegral_simultaneous_parity x₀ ℓ r h k c w N B hB e u
    (fun (ξ : activeBlocks (d := d) ℓ h → Bool) (i : I) => normalizedRoughChart x₀ ℓ r h k c w N ξ (u i))
    (fun ξ i => normalizedRoughChart_flip x₀ ℓ r h k c w N ξ (u i)) ζ η D (selectedOutcomeGhostTaper Q e τ u D)

theorem physicalGhostOutcomePatternWeight_bound (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ τ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (D : Degree (Fin Q) 3) :
    |physicalGhostOutcomePatternWeight Q x₀ ℓ r h k c w N τ B e u ζ η D| ≤
      ((1 + N₀ / c + 1 / N₀ ^ 2) ^ 4) ^ Q * ‖B‖ := by
  have hcz : 0 ≤ N₀ / c := by positivity
  have hcκ : 0 ≤ 1 / N₀ ^ 2 := by positivity
  have hb := ghostOutcomePatternIntegral_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough B e u
    (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i))
    (fun i => normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i))
    (1 + N₀ / c + 1 / N₀ ^ 2) (by linarith) (by linarith) (by linarith)
    (fun i => (normalizedRoughChart_scaled_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i)).trans
      (by linarith)) η D _ (selectedOutcomeGhostTaper_abs_le Q e τ u D)
  simpa only [Fintype.card_fin] using hb

theorem physicalGhostOutcomePatternWeight_one_sign_bound (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (c w N N₀ τ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (D : Degree (Fin Q) 3) (hD : ∀ v, D v ≠ 0 → ∃ i : I, e (Sum.inl i) = v)
    (j : activeBlocks (d := d) ℓ h) (η η' : activeBlocks (d := d) ℓ h → Bool)
    (he : ∀ i, i ≠ j → η i = η' i) :
    |physicalGhostOutcomePatternWeight Q x₀ ℓ r h k c w N τ B e u ζ η D -
      physicalGhostOutcomePatternWeight Q x₀ ℓ r h k c w N τ B e u ζ η' D| ≤
      ((1 + N₀ / c + 1 / N₀ ^ 2) ^ 4) ^ Q * (2 * ‖symbolPart j B‖ + (3 * ‖B - unit‖) *
        ((Fintype.card G : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d))) := by
  have hcz : 0 ≤ N₀ / c := by positivity
  have hcκ : 0 ≤ 1 / N₀ ^ 2 := by positivity
  have hb := ghostOutcomePatternIntegral_one_sign_bound x₀ ℓ r h k hℓ hr c w N N₀ hc hN₀ hN hm hrough
    B e u (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i))
    (fun i => normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i))
    (1 + N₀ / c + 1 / N₀ ^ 2) (by linarith) (by linarith) (by linarith)
    (fun i => (normalizedRoughChart_scaled_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i)).trans
      (by linarith)) D hD _ (selectedOutcomeGhostTaper_continuous Q e τ u D).aestronglyMeasurable
        (selectedOutcomeGhostTaper_abs_le Q e τ u D) j η η' he
  simpa only [Fintype.card_fin] using hb

end CausalLowerbound.PartC

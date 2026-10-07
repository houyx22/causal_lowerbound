import CausalLowerbound.PartC.GhostPatternParity
import CausalLowerbound.PartC.CompletedCubeTaper

/-! Ghost-integrated physical pattern weights with the actual graph taper
and actual retained rough variables. These are the weights in the completed
observation expansion; empty selected patterns carry no taper. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype G]

def selectedGhostTaper (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ)
    (u : I → d → ℝ) (S : Finset (Fin Q)) (g : G → d → ℝ) : ℝ :=
  if S = ∅ then 1 else completedCubeTaper Q e τ (u, g)

theorem selectedGhostTaper_continuous (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ)
    (u : I → d → ℝ) (S : Finset (Fin Q)) :
    Continuous (selectedGhostTaper Q e τ u S) := by
  change Continuous (fun g : G → d → ℝ => if S = ∅ then (1 : ℝ) else completedCubeTaper Q e τ (u, g))
  by_cases hS : S = ∅
  · simpa only [if_pos hS] using
      (continuous_const : Continuous (fun _ : G → d → ℝ => (1 : ℝ)))
  · simp only [if_neg hS]
    exact (completedCubeTaper_continuous Q e τ).comp
      ((continuous_const : Continuous (fun _ : G → d → ℝ => u)).prodMk continuous_id)

theorem selectedGhostTaper_abs_le (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ)
    (u : I → d → ℝ) (S : Finset (Fin Q)) (g : G → d → ℝ) :
    |selectedGhostTaper Q e τ u S g| ≤ 1 := by
  by_cases hS : S = ∅
  · simp only [selectedGhostTaper, if_pos hS, abs_one, le_refl]
  · rw [selectedGhostTaper, if_neg hS, abs_of_nonneg (completedCubeTaper_bounds Q e τ (u, g)).1]
    exact (completedCubeTaper_bounds Q e τ (u, g)).2

def physicalGhostPatternWeight (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N ja τ : ℝ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (S : Finset (Fin Q)) : ℝ :=
  ghostPatternIntegral x₀ ℓ r h k c w N ja B e u
    (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i)) η S (selectedGhostTaper Q e τ u S)

theorem physicalGhostPatternWeight_parity (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N ja τ : ℝ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (hB : reflection B = B) (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (S : Finset (Fin Q)) :
    physicalGhostPatternWeight Q x₀ ℓ r h k c w N ja τ B e u (Walsh.flip ζ) (Walsh.flip η) S =
      (-1) ^ S.card * physicalGhostPatternWeight Q x₀ ℓ r h k c w N ja τ B e u ζ η S := by
  unfold physicalGhostPatternWeight
  exact ghostPatternIntegral_simultaneous_parity x₀ ℓ r h k c w N ja B hB e u
    (fun (ξ : activeBlocks (d := d) ℓ h → Bool) (i : I) => normalizedRoughChart x₀ ℓ r h k c w N ξ (u i))
    (fun ξ i => normalizedRoughChart_flip x₀ ℓ r h k c w N ξ (u i)) ζ η S (selectedGhostTaper Q e τ u S)

theorem physicalGhostPatternWeight_bound (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ ja τ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hja : ja ^ 2 ≤ 1)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (S : Finset (Fin Q)) :
    |physicalGhostPatternWeight Q x₀ ℓ r h k c w N ja τ B e u ζ η S| ≤
      (1 + N₀ / c + 1 / (c * N₀)) ^ Q * ‖B‖ := by
  have hcz : 0 ≤ N₀ / c := by positivity
  have hcκ : 0 ≤ 1 / (c * N₀) := by positivity
  have hb := ghostPatternIntegral_bound x₀ ℓ r h k c w N N₀ ja hc hN₀ hN hm hrough hja B e u
    (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i))
    (fun i => normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i))
    (1 + N₀ / c + 1 / (c * N₀)) (by linarith) (by linarith) (by linarith)
    (fun i => (normalizedRoughChart_scaled_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i)).trans
      (by linarith)) η S _ (selectedGhostTaper_abs_le Q e τ u S)
  simpa only [Fintype.card_fin] using hb

theorem physicalGhostPatternWeight_one_sign_bound (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (c w N N₀ ja τ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hja : ja ^ 2 ≤ 1)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (S : Finset (Fin Q)) (hS : ∀ v ∈ S, ∃ i : I, e (Sum.inl i) = v)
    (j : activeBlocks (d := d) ℓ h) (η η' : activeBlocks (d := d) ℓ h → Bool)
    (he : ∀ i, i ≠ j → η i = η' i) :
    |physicalGhostPatternWeight Q x₀ ℓ r h k c w N ja τ B e u ζ η S -
      physicalGhostPatternWeight Q x₀ ℓ r h k c w N ja τ B e u ζ η' S| ≤
      (1 + N₀ / c + 1 / (c * N₀)) ^ Q * (2 * ‖symbolPart j B‖ + ‖B - unit‖ *
        ((Fintype.card G : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d))) := by
  have hcz : 0 ≤ N₀ / c := by positivity
  have hcκ : 0 ≤ 1 / (c * N₀) := by positivity
  have hb := ghostPatternIntegral_one_sign_bound x₀ ℓ r h k hℓ hr c w N N₀ ja hc hN₀ hN hm hrough hja
    B e u (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i))
    (fun i => normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i))
    (1 + N₀ / c + 1 / (c * N₀)) (by linarith) (by linarith) (by linarith)
    (fun i => (normalizedRoughChart_scaled_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i)).trans
      (by linarith)) S hS _ (selectedGhostTaper_continuous Q e τ u S).aestronglyMeasurable
        (selectedGhostTaper_abs_le Q e τ u S) j η η' he
  simpa only [Fintype.card_fin] using hb

end CausalLowerbound.PartC

import CausalLowerbound.PartC.GhostOutcomeTaperRemoval
import CausalLowerbound.PartC.ScalarComparisonParity

/-! Cubic graph-taper removal after shared resampling. Its geometric cost
retains shift times rough amplitude for scalar observation coefficients. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {K P d : Type*} [Fintype K] [Fintype P] [Fintype d] [DecidableEq d]

theorem physical_ghost_outcome_taper_scalar_bound
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : K → d → ℤ)
    (c w N N₀ τ shift rough C₀ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hfield : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (hshift : 0 ≤ shift) (hrough : 0 ≤ rough) (hr1 : rough ≤ 1) (hsr : shift ≤ rough) (hC₀ : 1 ≤ C₀)
    (I G : K → Type*) [∀ a, Fintype (I a)] [∀ a, Fintype (G a)]
    (e : ∀ a, I a ⊕ G a ≃ Fin Q) (u : ∀ a, I a → d → ℝ)
    (D : K → Degree (Fin Q) 3) (hD : 0 < ∑ a, degreeSize (D a))
    (B : K → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (hB : ∀ a, ‖B a‖ ≤ 2) (hreflect : ∀ a, reflection (B a) = B a)
    (T : Finset (activeBlocks (d := d) ℓ h))
    (g : P → (activeBlocks (d := d) ℓ h → Bool) → ℝ) (base : P → ℝ)
    (hg : ∀ i ζ, |g i ζ| ≤ C₀) (hb : ∀ i, |base i| ≤ C₀)
    (hgb : ∀ i ζ, |g i ζ - base i| ≤ C₀ * rough) :
    let C := 1 + N₀ / c + 1 / N₀ ^ 2
    let F := fun a ζ η => physicalGhostOutcomePatternWeight Q x₀ ℓ r h (k a) c w N τ (B a) (e a) (u a) ζ η (D a)
    let W := fun a ζ η => ghostOutcomePatternIntegral x₀ ℓ r h (k a) c w N (B a) (e a) (u a)
      (fun i => normalizedRoughChart x₀ ℓ r h (k a) c w N ζ (u a i)) η (D a) (fun _ => 1)
    |independentSigns.expect (fun ζ => shift ^ (∑ a, degreeSize (D a)) *
      Walsh.resampleAverage T (fun η => (∏ a, F a ζ η) - ∏ a, W a ζ η) ζ * ∏ i, g i ζ)| ≤
      ((2 * (C ^ 4) ^ Q) ^ Fintype.card K *
        ∑ a, (2 * (C ^ 4) ^ Q) * completedGhostTaperDefect Q (e a) τ (u a)) *
        (C₀ ^ Fintype.card P * ((Fintype.card P : ℝ) * C₀ + 1)) * (shift * rough) := by
  dsimp only
  let C := 1 + N₀ / c + 1 / N₀ ^ 2
  let M := 2 * (C ^ 4) ^ Q
  let F := fun a ζ η => physicalGhostOutcomePatternWeight Q x₀ ℓ r h (k a) c w N τ (B a) (e a) (u a) ζ η (D a)
  let W := fun a ζ η => ghostOutcomePatternIntegral x₀ ℓ r h (k a) c w N (B a) (e a) (u a)
    (fun i => normalizedRoughChart x₀ ℓ r h (k a) c w N ζ (u a i)) η (D a) (fun _ => 1)
  let cost := fun a => M * completedGhostTaperDefect Q (e a) τ (u a)
  have hcz : 0 ≤ N₀ / c := by positivity
  have hcκ : 0 ≤ 1 / N₀ ^ 2 := by positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCz : N₀ / c ≤ C := by dsimp [C]; linarith
  have hCκ : 1 / N₀ ^ 2 ≤ C := by dsimp [C]; linarith
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [one_le_pow₀ (one_le_pow₀ hC (n := 4)) (n := Q)]
  have hn (a : K) : (C ^ 4) ^ Q * ‖B a‖ ≤ M := by
    have hh := mul_le_mul_of_nonneg_left (hB a) (pow_nonneg (pow_nonneg (zero_le_one.trans hC) 4) Q)
    simpa only [M, mul_comm] using hh
  have hF (a : K) ζ η : |F a ζ η| ≤ M :=
    (physicalGhostOutcomePatternWeight_bound Q x₀ ℓ r h (k a) c w N N₀ τ hc hN₀ hN hm hfield
      (B a) (e a) (u a) ζ η (D a)).trans (hn a)
  have hW (a : K) ζ η : |W a ζ η| ≤ M := by
    have hh := ghostOutcomePatternIntegral_bound x₀ ℓ r h (k a) c w N N₀ hc hN₀ hN hm hfield
      (B a) (e a) (u a) _
      (fun i => normalizedRoughChart_bound x₀ ℓ r h (k a) c w N N₀ hc hN₀ hN hm hfield ζ (u a i))
      C hC hCz hCκ (fun i =>
        (normalizedRoughChart_scaled_bound x₀ ℓ r h (k a) c w N N₀ hc hN₀ hN hm hfield ζ (u a i)).trans hCz)
      η (D a) (fun _ => 1) (fun _ => by norm_num)
    apply le_trans ?_ (hn a)
    simpa only [Fintype.card_fin] using hh
  have hFp (a : K) ζ η : F a (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ degreeSize (D a) * F a ζ η :=
    physicalGhostOutcomePatternWeight_parity Q x₀ ℓ r h (k a) c w N τ (B a) (hreflect a) (e a) (u a) ζ η (D a)
  have hWp (a : K) ζ η : W a (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ degreeSize (D a) * W a ζ η :=
    ghostOutcomePatternIntegral_simultaneous_parity x₀ ℓ r h (k a) c w N (B a) (hreflect a) (e a) (u a)
      (fun ξ i => normalizedRoughChart x₀ ℓ r h (k a) c w N ξ (u a i))
      (fun ξ i => normalizedRoughChart_flip x₀ ℓ r h (k a) c w N ξ (u a i)) ζ η (D a) (fun _ => 1)
  have hcost (a : K) : 0 ≤ cost a :=
    mul_nonneg (zero_le_one.trans hM) (completedGhostTaperDefect_bounds Q (e a) τ (u a)).1
  have hdiff (a : K) ζ η : |F a ζ η - W a ζ η| ≤ cost a :=
    (physicalGhostOutcomePatternWeight_taper_removal_bound Q x₀ ℓ r h (k a) c w N N₀ τ hc hN₀ hN hm hfield
      (B a) (e a) (u a) ζ η (D a)).trans (mul_le_mul_of_nonneg_right (hn a)
        (completedGhostTaperDefect_bounds Q (e a) τ (u a)).1)
  exact resampled_product_comparison_scalar_shift_bound T (fun a => degreeSize (D a)) hD
    F W hFp hWp M hM hF hW cost hcost hdiff g base C₀ shift rough hC₀ hshift hrough hr1 hsr hg hb hgb

end CausalLowerbound.PartC

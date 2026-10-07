import CausalLowerbound.PartC.ScaledPropensityCarrier
import CausalLowerbound.PartC.MixedScaleBalance

/-! The degree-one physical carrier at the paper's mixed-rate scales.
The taper and assignment loss are chosen together with the volume budget;
the actual carrier bound vanishes while the ghost rate still vanishes
after multiplication by any fixed logarithmic power. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped BigOperators Topology Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

set_option maxHeartbeats 800000 in
theorem exists_rate_paperPropensityCarrier (Q : ℕ) [NeZero Q] (ρ θ α β γ ε a₀ : ℝ)
    (hρ : 0 < ρ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hreg : (α + β) * (2 + (Fintype.card d : ℝ) / γ) < Fintype.card d) (hε : 0 < ε)
    (hεsmall : ε < γ / Fintype.card d - rateExponent (α + β) (Fintype.card d) γ (effectiveSmoothness α β)) :
    let A := α + β
    let D := (Fintype.card d : ℝ)
    let s := effectiveSmoothness α β
    ∃ b : PowerBudget D (jitterExponent A D γ s ε) (rateMargin D γ s ε),
      ∃ c > 0, c ≤ 1 ∧ ∃ N₀ > 0, ∃ R > 0, ∃ C ≥ 0, ∃ K > 0,
        (∀ (x₀ : d → ℝ) (ℓ h : ℝ), 0 < ℓ → ℓ ≤ h →
          ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) ∧
        Tendsto (normalizedCarrierBound (Q.choose 2) (4 * Q) C R (jitterExponent A D γ s ε)
          b.taperGap (D * b.multiplierLoss)) atTop (𝓝 0) ∧
        (∀ B : ℝ, Tendsto (fun n : ℕ =>
          relaxedGhostMass A D γ s ε b.volumeExponent b.taperGap (n + 1) * PartB.logScale (n + 1) ^ B)
            atTop (𝓝 0)) ∧
        ∀ᶠ n : ℕ in atTop,
          let r := carrierScale A D ε n
          let h := coarseScale A D γ s ε n
          let t := jitterScale A D γ s ε n
          let ℓ := roughScale A D γ s ε n
          let N := carrierDegreeWeight R (D * b.multiplierLoss) t
          let τ := carrierTaper b.taperGap t
          let δ := normalizedCarrierBound (Q.choose 2) (4 * Q) C R (jitterExponent A D γ s ε)
            b.taperGap (D * b.multiplierLoss) n
          ∃ w : ℝ, 0 < w ∧ w ≤ 1 / 2 ∧
            t ^ Fintype.card d / 4 ≤ w ∧ w ≤ t ^ Fintype.card d / 2 ∧
            N₀ / c ≤ N ∧
            (∀ y : d → ℝ, assignmentMultiplier c w y * linearPartition y = assignmentPartition w y ∧
              0 ≤ assignmentMultiplier c w y ∧ assignmentMultiplier c w y ≤ 1 / c) ∧
            ∀ (x₀ : d → ℝ) (k : activeBlocks (d := d) r h),
              HasPaperPropensityCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ (a₀ * ℓ ^ α) t τ K δ := by
  dsimp only
  have hD : 0 < (Fintype.card d : ℝ) := by exact_mod_cast (Fintype.card_pos (α := d))
  have hs := effectiveSmoothness_pos α β hα hβ
  have hp := (concrete_scale_exponents (α + β) (Fintype.card d) γ (effectiveSmoothness α β) ε
    (add_pos hα hβ) hD hγ hs hreg hε hεsmall).2.2
  obtain ⟨b, hbudget⟩ := exists_relaxed_rate_control (α + β) (Fintype.card d) γ
    (effectiveSmoothness α β) ε (add_pos hα hβ) hD hγ hs hreg hε hεsmall
  obtain ⟨c, hc, hc1, N₀, hN₀, R, hR, C, hC, K, hK, hrough, hcarrier⟩ :=
    exists_scaled_paperPropensityCarrier (d := d) Q ρ θ b.multiplierLoss hρ hθ hθ1 b.multiplier_pos
  obtain ⟨hδlim, hevent⟩ := hcarrier (jitterExponent (α + β) (Fintype.card d) γ (effectiveSmoothness α β) ε)
    b.taperGap α a₀ hp b.gap_lt_one (by linarith [b.multiplier_small, b.gap_pos]) hα
  refine ⟨b, c, hc, hc1, N₀, hN₀, R, hR, C, hC, K, hK, hrough, hδlim, (fun B => (hbudget B).1), ?_⟩
  filter_upwards [hevent] with n hn
  obtain ⟨w, hw, hw1, hwlo, hwhi, hN, hm, hall⟩ := hn
  have hb := scales_balanced (α + β) (Fintype.card d) γ (effectiveSmoothness α β) ε
    (add_pos hα hβ) hD hγ hs hreg hε hεsmall n
  refine ⟨w, hw, hw1, hwlo, hwhi, hN, hm, fun x₀ k => ?_⟩
  exact hall x₀ _ _ hb.1 hb.2.1 hb.2.2.1 k

end CausalLowerbound.PartC

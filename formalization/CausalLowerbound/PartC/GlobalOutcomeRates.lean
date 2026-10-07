import CausalLowerbound.PartC.GlobalOutcomeCost
import CausalLowerbound.PartC.PropensityCostAlgebra

/-! The proved global degree-three cost vanishes under the actual mixed
design at the paper's scales. Carrier laws and their finite index sets
may vary with sample size; the constants in the bound do not. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Topology Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Nonempty d] [Fintype Ω]
  {K J : ℕ → Type*} [∀ n, Fintype (K n)] [∀ n, DecidableEq (K n)]
  [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]

theorem paper_outcomeGlobalCost_integral_tendsto
    (H₀ : DiscreteLaw ℕ) (q : ℕ) (α β γ ε θ a₀ b₀ c N₀ M κ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hβα : β ≤ α) (hγ : 0 < γ)
    (hreg : (α + β) * (2 + (Fintype.card d : ℝ) / γ) < Fintype.card d)
    (hε : 0 < ε) (hεsmall : ε < γ / Fintype.card d -
      rateExponent (α + β) (Fintype.card d) γ (effectiveSmoothness α β))
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (budget : PowerBudget (Fintype.card d)
      (jitterExponent (α + β) (Fintype.card d) γ (effectiveSmoothness α β) ε)
      (rateMargin (Fintype.card d) γ (effectiveSmoothness α β) ε))
    (F : ∀ n, ((K n → ℕ) × (J n → Bool)) → CarrierProfile d θ)
    (H : ∀ n, K n → DiscreteLaw ℕ)
    (kernel : ∀ n, K n → (J n → Bool) → ℕ → FiniteLaw Ω)
    (w : ℕ → ℝ)
    (hw : ∀ᶠ n in atTop, 0 < w n ∧
      w n ≤ jitterScale (α + β) (Fintype.card d) γ (effectiveSmoothness α β) ε n ^ Fintype.card d)
    (x₀ : d → ℝ) :
    let A := α + β
    let D := Fintype.card d
    let s := effectiveSmoothness α β
    let r := carrierScale A D ε
    let h := coarseScale A D γ s ε
    let t := jitterScale A D γ s ε
    let ℓ := roughScale A D γ s ε
    Tendsto (fun n => ∫ x : Fin (n + 1) → d → ℝ,
      outcomeGlobalCost H₀ (q + 1) x₀ (ℓ n) (r n) (h n) c N₀ M θ κ
        (a₀ * r n ^ α) (b₀ * ℓ n ^ β) (t n) (t n ^ (1 - budget.taperGap)) (w n) x
        ∂mixedCarrierDesign (F n) hθ hθ1 (activeBlocks (r n) (h n)) x₀ (r n) (H n) (kernel n) (n + 1))
      atTop (𝓝 0) := by
  let A := α + β
  let D := Fintype.card d
  let s := effectiveSmoothness α β
  let r := carrierScale A D ε
  let h := coarseScale A D γ s ε
  let t := jitterScale A D γ s ε
  let ℓ := roughScale A D γ s ε
  let CF := outcomeLocalFineConstant (q + 1) D c N₀ M θ κ
  let CC := outcomeLocalCrudeConstant (q + 1) D c N₀ θ κ
  let B := (designDensityCeiling d θ : ℝ)
  let CG := globalGhostConstant d q θ budget.volumeExponent
  have hD : 0 < (D : ℝ) := by exact_mod_cast (Fintype.card_pos (α := d))
  have hs : 0 < s := effectiveSmoothness_pos α β hα hβ
  have hb n := scales_balanced A D γ s ε (add_pos hα hβ) hD hγ hs hreg hε hεsmall n
  have hl n := roughScale_bounds A D γ s ε (add_pos hα hβ) hD hγ hs hreg hε hεsmall n
  have hamp n : (a₀ * r n ^ α) * t n * (b₀ * ℓ n ^ β) =
      (a₀ * b₀) * signalScale A D γ s ε n := by
    have he := (roughOutcome_scale_balance α β D γ ε hα hβ hβα hD hγ hreg hε hεsmall n).trans
      (coarseScale_power A D γ s ε hγ.ne' n)
    calc
      _ = (a₀ * b₀) * (r n ^ α * t n * ℓ n ^ β) := by ring
      _ = _ := by rw [he]
  apply tendsto_zero_of_propensityScalarCost_bound D A γ s ε (a₀ * b₀) CF CC B CG
    (add_pos hα hβ) hD hγ hs hreg hε hεsmall
    (outcomeLocalFineConstant_nonneg (q + 1) D c N₀ M θ κ)
    (outcomeLocalCrudeConstant_nonneg (q + 1) D c N₀ θ κ) (NNReal.coe_nonneg _) budget w
  · exact hw.mono (fun _ hn => hn.2)
  · exact Eventually.of_forall (fun n => integral_nonneg (fun x =>
      outcomeGlobalCost_nonneg H₀ (q + 1) x₀ (ℓ n) (r n) (h n) c N₀ M θ κ
        (a₀ * r n ^ α) (b₀ * ℓ n ^ β) (t n) (t n ^ (1 - budget.taperGap)) (w n) (hb n).1 x))
  · filter_upwards [hw] with n hwn
    have hw1 : w n ≤ 1 := hwn.2.trans (pow_le_one₀ (hb n).2.2.2.1.le (hb n).2.2.2.2.1)
    have hnr : ((n + 1 : ℕ) : ℝ) * r n ^ D ≤ 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        carrierScale_sparse D (Fintype.card_pos (α := d)) A ε (add_pos hα hβ) hε.le n
    have he := outcomeGlobalCost_integral_le H₀ q x₀ (ℓ n) (r n) (h n) c N₀ M κ
      (a₀ * r n ^ α) (b₀ * ℓ n ^ β) (t n) (t n ^ (1 - budget.taperGap)) (w n)
      (hl n).1.le (hb n).1 (hb n).2.1 hwn.1 hw1 budget.volumeExponent budget.volume_pos
      budget.volume_lt (Real.rpow_pos_of_pos (hb n).2.2.2.1 _) (F n) hθ hθ1 (H n) (kernel n) (n + 1) hnr
    dsimp only at he
    rw [hamp n] at he
    simpa only [Nat.cast_add, Nat.cast_one, propensityScalarCost] using he

end CausalLowerbound.PartC


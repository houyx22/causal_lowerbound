import CausalLowerbound.PartB.PaperScales
import CausalLowerbound.PartB.PhysicalJointComparison

/-! One fixed positive amplitude makes the complete polynomial family legal. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped Classical
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def PaperLegalFamily (Q : ℕ) (ρ : ℝ) (α β γ : Regularity) (ε c : ℝ)
    (x₀ : d → ℝ) (Lπ L₀ Lτ κ : ℝ) : Prop :=
  let A := α.exponent + β.exponent
  let D := (Fintype.card d : ℝ)
  ∀ (n : ℕ) (side : Bool)
    (z : activeBlocks (d := d) (paperFineScale A D ε n) (paperCoarseScale A D γ.exponent ε n) →
      MomentGrid (CoefficientExponent d Q) (4 * Q)),
    let r := paperFineScale A D ε n
    let h := paperCoarseScale A D γ.exponent ε n
    let t := paperJitterScale A D γ.exponent ε n
    let a := c * r ^ α.exponent
    let b := c * r ^ β.exponent
    (modelFields side (activeBlocks r h)
      (fun k => paperCoefficientAtoms Q ρ (extendBlockSample (activeBlocks r h) z k))
      x₀ r h a b t (a * b * t ^ 2)).Legal α β γ Lπ L₀ Lτ κ

theorem exists_paper_legal_family [Nonempty d] (Q : ℕ) (ρ : ℝ)
    (α β γ : Regularity) (ε : ℝ) (x₀ : d → ℝ)
    (hA : 0 < α.exponent + β.exponent) (hγ : 0 < γ.exponent)
    (hβγ : β.exponent ≤ γ.exponent)
    (hreg : (α.exponent + β.exponent) * (2 + (Fintype.card d : ℝ) / γ.exponent) < Fintype.card d)
    (hε : 0 < ε) (hεsmall : ε < γ.exponent / Fintype.card d - rateExponent (α.exponent + β.exponent) (Fintype.card d) γ.exponent)
    (Lπ L₀ Lτ κ : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀) (hLτ : 0 < Lτ) (hκ : κ < 1 / 4) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ PaperLegalFamily Q ρ α β γ ε c x₀ Lπ L₀ Lτ κ := by
  have hD : 0 < (Fintype.card d : ℝ) := by exact_mod_cast (Fintype.card_pos (α := d))
  obtain ⟨e, he, he1, hl⟩ := exists_legal_amplitudes (paperCoefficientAtoms (d := d) Q ρ)
    α β γ hβγ Lπ L₀ Lτ κ hLπ hL₀ hLτ hκ
  refine ⟨e / 2, by positivity, by linarith, ?_⟩
  intro n side z
  have hs := paper_scales_balanced α.exponent β.exponent (Fintype.card d) γ.exponent ε
    hA hD hγ hreg hε hεsmall n
  have hb := paper_target_balance α.exponent β.exponent (Fintype.card d) γ.exponent ε (e / 2) (e / 2)
    hA hD hγ hreg hε hεsmall n
  rw [← paper_coarse_signal (α.exponent + β.exponent) (Fintype.card d) γ.exponent ε hγ.ne' n] at hb
  dsimp only
  rw [hb]
  exact hl (e / 2) (e / 2) (by positivity) (by linarith) (by positivity) (by linarith)
    side _ (extendBlockSample _ z) x₀ _ _ _ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2

def paperComparisonDensity (Q : ℕ) (ρ : ℝ) (α β γ : Regularity) (ε c θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (Lπ L₀ Lτ κ : ℝ) (hκ : 0 ≤ κ)
    (hlegal : PaperLegalFamily Q ρ α β γ ε c x₀ Lπ L₀ Lτ κ)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (n : ℕ) (side : Bool) :
    DensityLaw ((mixedDesignExperiment Q
      (activeBlocks (paperFineScale (α.exponent + β.exponent) (Fintype.card d) ε n)
        (paperCoarseScale (α.exponent + β.exponent) (Fintype.card d) γ.exponent ε n))
      θ hθ hθ1 H kernel x₀ (paperFineScale (α.exponent + β.exponent) (Fintype.card d) ε n) (n + 1)).prod
      (Measure.count : Measure (Fin (n + 1) → Bool × Bool))) :=
  let A := α.exponent + β.exponent
  let D := (Fintype.card d : ℝ)
  let r := paperFineScale A D ε n
  let h := paperCoarseScale A D γ.exponent ε n
  let t := paperJitterScale A D γ.exponent ε n
  let a := c * r ^ α.exponent
  let b := c * r ^ β.exponent
  physicalComparisonDensity side (activeBlocks r h) (paperCoefficientAtoms Q ρ) (paperCoefficientLaw Q)
    H kernel θ hθ hθ1 x₀ r h a b t (a * b * t ^ 2) (hlegal n side) hκ (n + 1)

end CausalLowerbound.PartB.ShellGeometry

import CausalLowerbound.PartC.PropensityMinimax
import CausalLowerbound.PartC.OutcomeMinimax

/-! Part C: both mixed smoothness regimes in the original statistical
model, with an arbitrary positive epsilon loss in the paper rate. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology ENNReal
namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

theorem paper_partC_minimax (α β γ : Regularity) (ε : ℝ) (x₀ : d → ℝ)
    (hα : 0 < α.exponent) (hβ : 0 < β.exponent) (hγ : 0 < γ.exponent)
    (hmixed : (α.exponent ≤ 1 ∧ 1 < β.exponent) ∨ (β.exponent ≤ 1 ∧ 1 < α.exponent))
    (hreg : (α.exponent + β.exponent) * (2 + (Fintype.card d : ℝ) / γ.exponent) < Fintype.card d)
    (hε : 0 < ε)
    (Lπ L₀ Lτ κ lower upper : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀) (hLτ : 0 < Lτ)
    (hκ : 0 < κ) (hκ1 : κ < 1 / 4) (hlo : lower < 1) (hhi : 1 < upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (C * (n : ℝ) ^ (-(rateExponent (α.exponent + β.exponent)
        (Fintype.card d) γ.exponent (effectiveSmoothness α.exponent β.exponent) + ε))) ≤
        minimaxRisk α β γ Lπ L₀ Lτ κ lower upper hκ.le x₀ n := by
  rcases hmixed with h | h
  · exact paper_partC_roughPropensity_minimax α β γ ε x₀ hα h.1 h.2 hγ hreg hε
      Lπ L₀ Lτ κ lower upper hLπ hL₀ hLτ hκ hκ1 hlo hhi
  · exact paper_partC_roughOutcome_minimax α β γ ε x₀ h.2 hβ h.1 hγ hreg hε
      Lπ L₀ Lτ κ lower upper hLπ hL₀ hLτ hκ hκ1 hlo hhi

end CausalLowerbound.PartC

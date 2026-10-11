import CausalLowerbound.UniformLowerBound.Minimax

/-! Part A of the rough-design lower bound.  The exactly uniform design is
a legal submodel of every design class whose bounds contain one.  In the
regime 0 < alpha,beta <= 1 the original exponent equals the exact uniform
exponent, so this implication incurs no epsilon loss. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal

namespace CausalLowerbound.PartA
open PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt

def effectiveSmoothness (α β : ℝ) : ℝ := (min α 1 + min β 1) / 2

def rateExponent (α β d γ : ℝ) : ℝ :=
  (α + β + 2 * effectiveSmoothness α β) /
    (d + 4 * effectiveSmoothness α β + 2 * d * effectiveSmoothness α β / γ)

theorem rateExponent_eq_uniform (α β d γ : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hα1 : α ≤ 1) (hβ1 : β ≤ 1) (hd : 0 < d) (hγ : 0 < γ) :
    rateExponent α β d γ = UniformLowerBound.rateExponent (α + β) d γ := by
  rw [UniformLowerBound.rateExponent_eq_balanced (α + β) d γ (add_pos hα hβ) hd hγ]
  unfold rateExponent effectiveSmoothness
  rw [min_eq_left hα1, min_eq_left hβ1]
  congr 1 <;> ring

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-- The original Part A lower bound for every positive sample size, without
an epsilon loss. The risk supremum is over the complete rough-design model
and the infimum is over all measurable estimators. -/
theorem paper_partA_minimax (α β γ : Regularity) (x₀ : d → ℝ)
    (hα : 0 < α.exponent) (hβ : 0 < β.exponent)
    (hα1 : α.exponent ≤ 1) (hβ1 : β.exponent ≤ 1) (hγ : 0 < γ.exponent)
    (hreg : (α.exponent + β.exponent) * (2 + (Fintype.card d : ℝ) / γ.exponent) < Fintype.card d)
    (Lπ L₀ Lτ κ lower upper : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀)
    (hLτ : 0 < Lτ) (hκ : 0 < κ) (hκ1 : κ < 1 / 4)
    (hl : lower < 1) (hu : 1 < upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (C * (n : ℝ) ^
        (-rateExponent α.exponent β.exponent (Fintype.card d) γ.exponent)) ≤
          minimaxRisk α β γ Lπ L₀ Lτ κ lower upper hκ.le x₀ n := by
  have hd : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos (α := d)
  have hκhalf : κ < 1 / 2 := by linarith
  obtain ⟨C, hC, hbound⟩ := UniformLowerBound.paper_uniform_minimax α β γ x₀
    hα hβ hγ hreg Lπ L₀ Lτ κ hLπ hL₀ hLτ hκ hκhalf
  refine ⟨C, hC, ?_⟩
  intro n hn
  rw [rateExponent_eq_uniform α.exponent β.exponent (Fintype.card d) γ.exponent
    hα hβ hα1 hβ1 hd hγ]
  exact (hbound n hn).trans (UniformLowerBound.uniformMinimaxRisk_le α β γ
    Lπ L₀ Lτ κ lower upper hκ.le hl.le hu.le x₀ n)

end CausalLowerbound.PartA

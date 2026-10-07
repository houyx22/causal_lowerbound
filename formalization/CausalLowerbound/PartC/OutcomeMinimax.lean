import CausalLowerbound.PartC.OutcomePaperMinimax

/-! The original degree-three mixed-case minimax rate for every positive
epsilon. No carrier, regularity, matching, or TV bound is an input. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology ENNReal
namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

theorem paper_partC_roughOutcome_minimax (α β γ : Regularity) (ε : ℝ) (x₀ : d → ℝ)
    (hα : 1 < α.exponent) (hβ : 0 < β.exponent) (hβ1 : β.exponent ≤ 1) (hγ : 0 < γ.exponent)
    (hreg : (α.exponent + β.exponent) * (2 + (Fintype.card d : ℝ) / γ.exponent) < Fintype.card d)
    (hε : 0 < ε)
    (Lπ L₀ Lτ κ lower upper : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀) (hLτ : 0 < Lτ)
    (hκ : 0 < κ) (hκ1 : κ < 1 / 4) (hlo : lower < 1) (hhi : 1 < upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (C * (n : ℝ) ^ (-(rateExponent (α.exponent + β.exponent)
        (Fintype.card d) γ.exponent (effectiveSmoothness α.exponent β.exponent) + ε))) ≤
        minimaxRisk α β γ Lπ L₀ Lτ κ lower upper hκ.le x₀ n := by
  let A := α.exponent + β.exponent
  let D := (Fintype.card d : ℝ)
  let s := effectiveSmoothness α.exponent β.exponent
  have hA : 0 < A := by dsimp only [A]; linarith
  have hD : 0 < D := by dsimp only [D]; exact_mod_cast (Fintype.card_pos (α := d))
  have hs : 0 < s := effectiveSmoothness_pos _ _ (by linarith) hβ
  have hgap : 0 < γ.exponent / D - rateExponent A D γ.exponent s :=
    sub_pos.mpr (rate_ordering A D γ.exponent s hA hD hγ hs hreg).2.2.1
  let e := min ε (γ.exponent / D - rateExponent A D γ.exponent s) / 2
  have he : 0 < e := by dsimp only [e]; positivity
  have heε : e ≤ ε := by
    have hh := min_le_left ε (γ.exponent / D - rateExponent A D γ.exponent s)
    dsimp only [e]
    linarith
  have hesmall : e < γ.exponent / D - rateExponent A D γ.exponent s := by
    have hh := min_le_right ε (γ.exponent / D - rateExponent A D γ.exponent s)
    dsimp only [e]
    linarith
  obtain ⟨C, hC, hb⟩ := paper_partC_roughOutcome_minimax_small_epsilon α β γ e x₀
    hα hβ hβ1 hγ hreg he hesmall Lπ L₀ Lτ κ lower upper hLπ hL₀ hLτ hκ hκ1 hlo hhi
  have hb' : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (C * signalScale A D γ.exponent s ε n) ≤
      minimaxRisk α β γ Lπ L₀ Lτ κ lower upper hκ.le x₀ (n + 1) := by
    filter_upwards [hb] with n hn
    apply le_trans _ hn
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_left (Nat.cast_nonneg n)) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb'
  refine ⟨C, hC, eventually_atTop.mpr ⟨N + 1, ?_⟩⟩
  intro n hn
  have hnn : n - 1 + 1 = n := by omega
  have hnR : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hnn
  have hh := hN (n - 1) (by omega)
  simpa only [signalScale, hnR, hnn] using hh

end CausalLowerbound.PartC


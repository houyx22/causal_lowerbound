import CausalLowerbound.PartB.MinimaxReduction
import CausalLowerbound.PartB.PaperActualTV

/-! Part B: the actual minimax lower bound, with all analytic, geometric,
probabilistic and model-class inputs discharged by the explicit construction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory Filter
open scoped Topology Classical ENNReal
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

theorem paper_partB_minimax_small_epsilon (α β γ : Regularity) (ε : ℝ) (x₀ : d → ℝ)
    (hA : 0 < α.exponent + β.exponent) (hγ : 0 < γ.exponent) (hβγ : β.exponent ≤ γ.exponent)
    (hreg : (α.exponent + β.exponent) * (2 + (Fintype.card d : ℝ) / γ.exponent) < Fintype.card d)
    (hε : 0 < ε) (hεsmall : ε < γ.exponent / Fintype.card d - rateExponent (α.exponent + β.exponent) (Fintype.card d) γ.exponent)
    (Lπ L₀ Lτ κ lower upper : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀) (hLτ : 0 < Lτ)
    (hκ : 0 < κ) (hκ1 : κ < 1 / 4) (hl : lower < 1) (hu : 1 < upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (C * paperSignalScale (α.exponent + β.exponent) (Fintype.card d) γ.exponent ε n) ≤
        minimaxRisk α β γ Lπ L₀ Lτ κ lower upper hκ.le x₀ (n + 1) := by
  let A := α.exponent + β.exponent
  let D := (Fintype.card d : ℝ)
  let Q := matchingOrder D γ.exponent (rateExponent A D γ.exponent + ε) (D * ε / (2 * A))
  have hQ : 2 ≤ Q := matchingOrder_ge_two _ _ _ _
  letI : NeZero Q := ⟨by omega⟩
  have hD : 0 < D := by dsimp only [D]; exact_mod_cast (Fintype.card_pos (α := d))
  obtain ⟨θ, hθ, hθ1, hθlo, hθhi⟩ := exists_design_contrast (5 ^ Fintype.card d) lower upper hl hu
  obtain ⟨c, hc, hc1, hlegal⟩ := exists_paper_legal_family Q 1 α β γ ε x₀ hA hγ hβγ hreg hε hεsmall
    Lπ L₀ Lτ κ hLπ hL₀ hLτ hκ1
  let B := ((Q.choose 2 : ℝ) + 2) / 2 + 1
  have hB : ((Q.choose 2 : ℝ) + 2) / 2 < B := by dsimp only [B]; linarith
  obtain ⟨H, kernel, _, hTV⟩ := paper_actual_totalVariation_tendsto Q 1 α β γ ε c θ B x₀
    (by norm_num) hA hγ hreg hε hεsmall hc hc1 hθ hθ1 hB rfl Lπ L₀ Lτ κ hκ hlegal
  refine ⟨c * c / 4, by positivity, ?_⟩
  filter_upwards [hTV.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n htv
  let r := paperFineScale A D ε n
  let h := paperCoarseScale A D γ.exponent ε n
  let t := paperJitterScale A D γ.exponent ε n
  let a := c * r ^ α.exponent
  let b := c * r ^ β.exponent
  have hbal := paper_target_balance α.exponent β.exponent D γ.exponent ε c c hA hD hγ hreg hε hεsmall n
  change a * b * t ^ 2 = c * c * paperSignalScale A D γ.exponent ε n at hbal
  have hδ : 0 ≤ a * b * t ^ 2 := by
    rw [hbal]
    exact mul_nonneg (mul_nonneg hc.le hc.le) (Real.rpow_nonneg (by positivity) _)
  have hd (labels : activeBlocks (d := d) r h → ℕ) :
      DesignLegal lower upper (normalizedDesign Q (activeBlocks r h) θ (extendLabels _ labels) x₀ r) := by
    have he := normalizedDesign_legal Q (activeBlocks r h) θ hθ.le hθ1 (extendLabels _ labels) x₀ r
    exact ⟨he.1, he.2.1, fun x => ⟨hθlo.trans (he.2.2 x).1, (he.2.2 x).2.trans hθhi⟩⟩
  have he := physicalComparison_minimax_lower (activeBlocks r h) (paperCoefficientAtoms Q 1) (paperCoefficientLaw Q)
    (H n) (kernel n) θ hθ.le hθ1 x₀ r h a b t (a * b * t ^ 2) hδ (hlegal n) hd hκ.le (n + 1) htv.le
  rw [hbal] at he
  convert he using 1
  congr 1
  ring

/-- The Part B minimax rate for every positive epsilon. The supremum ranges
over legal designs and regular Bernoulli regression models; the infimum
ranges over all measurable estimators, with infinite risks allowed. -/
theorem paper_partB_minimax (α β γ : Regularity) (ε : ℝ) (x₀ : d → ℝ)
    (hα : 1 < α.exponent) (hβ : 1 < β.exponent) (hγ : 0 < γ.exponent)
    (hreg : (α.exponent + β.exponent) * (2 + (Fintype.card d : ℝ) / γ.exponent) < Fintype.card d)
    (hε : 0 < ε)
    (Lπ L₀ Lτ κ lower upper : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀) (hLτ : 0 < Lτ)
    (hκ : 0 < κ) (hκ1 : κ < 1 / 4) (hl : lower < 1) (hu : 1 < upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (C * (n : ℝ) ^ (-(rateExponent (α.exponent + β.exponent) (Fintype.card d) γ.exponent + ε))) ≤
        minimaxRisk α β γ Lπ L₀ Lτ κ lower upper hκ.le x₀ n := by
  let A := α.exponent + β.exponent
  let D := (Fintype.card d : ℝ)
  have hA : 0 < A := by dsimp only [A]; linarith
  have hD : 0 < D := by dsimp only [D]; exact_mod_cast (Fintype.card_pos (α := d))
  have hβγ : β.exponent ≤ γ.exponent := by
    have hh := (rate_ordering A D γ.exponent hA hD hγ hreg).1
    dsimp only [A] at hh
    linarith
  have hgap : 0 < γ.exponent / D - rateExponent A D γ.exponent :=
    sub_pos.mpr (rate_ordering A D γ.exponent hA hD hγ hreg).2.2.1
  let e := min ε (γ.exponent / D - rateExponent A D γ.exponent) / 2
  have he : 0 < e := by dsimp only [e]; positivity
  have heε : e ≤ ε := by
    have hh := min_le_left ε (γ.exponent / D - rateExponent A D γ.exponent)
    dsimp only [e]
    linarith
  have hesmall : e < γ.exponent / D - rateExponent A D γ.exponent := by
    have hh := min_le_right ε (γ.exponent / D - rateExponent A D γ.exponent)
    dsimp only [e]
    linarith
  obtain ⟨C, hC, hb⟩ := paper_partB_minimax_small_epsilon α β γ e x₀ hA hγ hβγ hreg he hesmall
    Lπ L₀ Lτ κ lower upper hLπ hL₀ hLτ hκ hκ1 hl hu
  have hb' : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (C * paperSignalScale A D γ.exponent ε n) ≤
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
  simpa only [paperSignalScale, hnR, hnn] using hh

end CausalLowerbound.PartB.ShellGeometry

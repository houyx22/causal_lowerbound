import CausalLowerbound.UniformLowerBound.ActualComparison
import CausalLowerbound.UniformLowerBound.Legality
import CausalLowerbound.UniformLowerBound.ScaleChoice

/-! The uniform-covariate minimax lower bound. All model construction,
moment cancellation, component probabilities, and information bounds are
discharged internally. The conclusion has no epsilon loss. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped Classical ENNReal

namespace CausalLowerbound.UniformLowerBound
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

theorem paper_uniform_minimax (α β γ : Regularity) (x₀ : d → ℝ)
    (hα : 0 < α.exponent) (hβ : 0 < β.exponent) (hγ : 0 < γ.exponent)
    (hreg : (α.exponent + β.exponent) * (2 + (Fintype.card d : ℝ) / γ.exponent) < Fintype.card d)
    (Lπ L₀ Lτ κ : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀) (hLτ : 0 < Lτ)
    (hκ : 0 < κ) (hκ1 : κ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (C * (n : ℝ) ^
        (-rateExponent (α.exponent + β.exponent) (Fintype.card d) γ.exponent)) ≤
          uniformMinimaxRisk α β γ Lπ L₀ Lτ κ hκ.le x₀ n := by
  let A := α.exponent + β.exponent
  let D : ℝ := Fintype.card d
  have hA : 0 < A := add_pos hα hβ
  have hD : 0 < D := by dsimp [D]; exact_mod_cast Fintype.card_pos (α := d)
  have hβγ : β.exponent ≤ γ.exponent := by
    have hh := (PartB.rate_ordering A D γ.exponent hA hD hγ hreg).1
    dsimp [A] at hh
    linarith
  obtain ⟨ε, hε, hε1, hlegal⟩ := exists_legal_amplitudes (d := d) α β γ hβγ
    Lπ L₀ Lτ κ hLπ hL₀ hLτ hκ1
  let c := ε / 2
  have hc : 0 < c := div_pos hε two_pos
  have hcε : c ≤ ε := by dsimp [c]; linarith
  have hc1 : c ≤ 1 := hcε.trans hε1
  let Q := componentCutoff A D γ.exponent
  have hQ : 1 ≤ Q := (by norm_num : 1 ≤ 2).trans (componentCutoff_ge_two A D γ.exponent)
  let K := actualComparisonConstant d κ Q
  have hK : 0 ≤ K := actualComparisonConstant_nonneg κ hκ Q
  obtain ⟨t, ht, ht1, hcal⟩ := exists_calibrated_scales A D γ.exponent
    (clusterConstant d Q) (2 * K) hA hD hγ hreg (clusterConstant_nonneg Q)
  refine ⟨c ^ 2 * t ^ γ.exponent, mul_pos (sq_pos_of_pos hc) (Real.rpow_pos_of_pos ht _), ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let h := coarseScale A D γ.exponent t n
  let ℓ := fineScale A D γ.exponent t n
  let a := c * ℓ ^ α.exponent
  let b := c * ℓ ^ β.exponent
  let regime : Bool := decide (α.exponent ≤ β.exponent)
  obtain ⟨hℓ, hℓh, hht, hh1, hbal⟩ := scales_valid A D γ.exponent t n
    hA hD hγ hreg ht ht1 hn1
  change 0 < ℓ at hℓ
  change ℓ ≤ h at hℓh
  change h ≤ 1 at hh1
  have hh : 0 < h := hℓ.trans_le hℓh
  have hℓ1 : ℓ ≤ 1 := hℓh.trans hh1
  have ha : 0 ≤ a := mul_nonneg hc.le (Real.rpow_nonneg hℓ.le _)
  have hb : 0 ≤ b := mul_nonneg hc.le (Real.rpow_nonneg hℓ.le _)
  have ha1 : a ≤ 1 := mul_le_one₀ hc1 (Real.rpow_nonneg hℓ.le _)
    (Real.rpow_le_one hℓ.le hℓ1 hα.le)
  have hb1 : b ≤ 1 := mul_le_one₀ hc1 (Real.rpow_nonneg hℓ.le _)
    (Real.rpow_le_one hℓ.le hℓ1 hβ.le)
  let S := activeBlocks (d := d) ℓ h
  have hfields (side : Bool) (ζ : S → Bool) :
      (fields regime side S (extendBlockSample S ζ) x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ :=
    hlegal c c hc.le hcε hc.le hcε regime side S (extendBlockSample S ζ)
      x₀ ℓ h hℓ hℓh hh1 hbal.symm
  let family := actualFamily regime S x₀ ℓ h a b hfields
  have hinfo := actual_totalVariation_bound regime Q hQ x₀ ℓ h a b
    hℓ hℓh ha ha1 hb hb1 hκ hfields n
  have hmono :
      K * (a ^ 2 * b ^ 2 + (if regime then b ^ 4 else a ^ 4)) *
        (n : ℝ) ^ 2 * h ^ Fintype.card d * ℓ ^ Fintype.card d ≤
      (2 * K) * ((n : ℝ) ^ (2 : ℝ) * h ^ D * ℓ ^ (D + 2 * A)) := by
    simpa only [a, b, regime, decide_eq_true_eq, D, A, mul_assoc] using
      component_monomial_le α.exponent β.exponent c ℓ h n K (Fintype.card d)
        hc.le hc1 hℓ hℓ1 hh.le hK
  have htv : (uniformMixtureDensity (signPrior S) (family true) hκ.le n).totalVariation
      (uniformMixtureDensity (signPrior S) (family false) hκ.le n) ≤ 1 / 2 := by
    apply hinfo.trans
    apply (add_le_add_left (Real.sqrt_le_sqrt hmono) _).trans
    have hcaln := hcal n hn1
    change clusterConstant d Q * ((n : ℝ) ^ ((Q : ℝ) + 1) * h ^ D * ℓ ^ ((Q : ℝ) * D)) +
      Real.sqrt ((2 * K) * ((n : ℝ) ^ (2 : ℝ) * h ^ D * ℓ ^ (D + 2 * A))) ≤ 1 / 2 at hcaln
    rw [show (Q : ℝ) + 1 = ((Q + 1 : ℕ) : ℝ) by simp,
      show (Q : ℝ) * D = ((Q * Fintype.card d : ℕ) : ℝ) by simp [D]] at hcaln
    simpa only [D, Real.rpow_natCast, Real.rpow_two] using hcaln
  have htarget (side : Bool) (ζ : S → Bool) :
      (family side ζ).fields.effect x₀ = if side then 4 * a * b else 0 := by
    simp [family, actualFamily, uniformStatisticalModel, fields, targetField_center]
  have hrisk := uniformComparison_minimax_lower (signPrior S) family hκ.le x₀ n
    (4 * a * b) (by positivity) htarget htv
  have hsignal : (4 * a * b) / 4 =
      (c ^ 2 * t ^ γ.exponent) * (n : ℝ) ^ (-rateExponent A D γ.exponent) := by
    calc
      _ = a * b := by ring
      _ = _ := amplitude_signal α.exponent β.exponent D γ.exponent c t n
        hA hD hγ hreg ht ht1 hn1
  rw [hsignal] at hrisk
  exact hrisk

/-- The exponent in the notation of the attached uniform-design manuscript. -/
theorem paper_uniform_minimax_explicit (α β γ : Regularity) (x₀ : d → ℝ)
    (hα : 0 < α.exponent) (hβ : 0 < β.exponent) (hγ : 0 < γ.exponent)
    (hreg : (α.exponent + β.exponent) * (2 + (Fintype.card d : ℝ) / γ.exponent) < Fintype.card d)
    (Lπ L₀ Lτ κ : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀) (hLτ : 0 < Lτ)
    (hκ : 0 < κ) (hκ1 : κ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (C * (n : ℝ) ^
        (-(1 / (1 + (Fintype.card d : ℝ) / (2 * γ.exponent) +
          (Fintype.card d : ℝ) / (2 * (α.exponent + β.exponent)))))) ≤
          uniformMinimaxRisk α β γ Lπ L₀ Lτ κ hκ.le x₀ n := by
  simpa only [rateExponent_eq (α.exponent + β.exponent) (Fintype.card d) γ.exponent
    (add_pos hα hβ) (by exact_mod_cast Fintype.card_pos (α := d)) hγ] using
    paper_uniform_minimax α β γ x₀ hα hβ hγ hreg Lπ L₀ Lτ κ hLπ hL₀ hLτ hκ hκ1

end CausalLowerbound.UniformLowerBound

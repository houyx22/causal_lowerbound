import CausalLowerbound.PartC.PropensityFiniteMinimax
import CausalLowerbound.PartC.PropensityRateEnvelope
import CausalLowerbound.PartC.RatePropensityCarrier
import CausalLowerbound.PartC.BoundedPropensityWitness
import CausalLowerbound.PartC.PaperCarriedBounds
import CausalLowerbound.PartC.MixedModelLegality
import CausalLowerbound.PartB.SmallDensityCarrier

/-! The degree-one mixed-case minimax theorem. All carrier, matching,
legality, and information conditions are discharged by the construction. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open MeasureTheory Filter
open scoped Topology Classical ENNReal
namespace CausalLowerbound.PartC
open PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

theorem paper_partC_roughPropensity_minimax_small_epsilon
    (α β γ : Regularity) (ε : ℝ) (x₀ : d → ℝ)
    (hα : 0 < α.exponent) (hα1 : α.exponent ≤ 1) (hβ : 1 < β.exponent) (hγ : 0 < γ.exponent)
    (hreg : (α.exponent + β.exponent) * (2 + (Fintype.card d : ℝ) / γ.exponent) < Fintype.card d)
    (hε : 0 < ε) (hεsmall : ε < γ.exponent / Fintype.card d -
      rateExponent (α.exponent + β.exponent) (Fintype.card d) γ.exponent (effectiveSmoothness α.exponent β.exponent))
    (Lπ L₀ Lτ κ lower upper : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀) (hLτ : 0 < Lτ)
    (hκ : 0 < κ) (hκ1 : κ < 1 / 4) (hlo : lower < 1) (hhi : 1 < upper) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (C * signalScale (α.exponent + β.exponent) (Fintype.card d) γ.exponent
        (effectiveSmoothness α.exponent β.exponent) ε n) ≤
        minimaxRisk α β γ Lπ L₀ Lτ κ lower upper hκ.le x₀ (n + 1) := by
  let A := α.exponent + β.exponent
  let D := Fintype.card d
  let s := effectiveSmoothness α.exponent β.exponent
  have hβ0 : 0 < β.exponent := by linarith
  have hαβ : α.exponent ≤ β.exponent := hα1.trans hβ.le
  have hA : 0 < A := add_pos hα hβ0
  have hD : 0 < (D : ℝ) := by exact_mod_cast (Fintype.card_pos (α := d))
  have hs : 0 < s := effectiveSmoothness_pos _ _ hα hβ0
  let q := matchingOrder A D γ.exponent s ε - 1
  let Q := q + 1
  have hQorder : Q = matchingOrder A D γ.exponent s ε := by
    have := matchingOrder_ge_two A D γ.exponent s ε
    dsimp only [Q, q]
    omega
  letI : NeZero Q := ⟨by dsimp only [Q]; omega⟩
  obtain ⟨θ, hθ, hθ1, hθlo, hθhi⟩ := exists_design_contrast (5 ^ D) lower upper hlo hhi
  obtain ⟨eL, heL, heL1, hmodels⟩ := exists_roughPropensity_legal_amplitude
    (paperCoefficientAtoms (d := d) Q 1) α β γ Lπ L₀ Lτ κ hLπ hL₀ hLτ hκ1
  obtain ⟨eS, heS, heS1, hsmooth⟩ := exists_paperCarried_small_amplitude (d := d) Q 1
  let a₀ := min eL eS / 2
  have ha₀ : 0 < a₀ := by dsimp only [a₀]; positivity
  have haL : a₀ ≤ eL := by dsimp only [a₀]; linarith [min_le_left eL eS, lt_min heL heS]
  have haS : a₀ ≤ eS := by dsimp only [a₀]; linarith [min_le_right eL eS, lt_min heL heS]
  have ha1 : a₀ ≤ 1 := haL.trans heL1
  obtain ⟨budget, c, hc, hc1, N₀, hN₀, R₀, hR₀, C₀, hC₀, K₀, hK₀, hrough, hδlim, _, hcarrier⟩ :=
    exists_rate_paperPropensityCarrier (d := d) Q 1 θ α.exponent β.exponent γ.exponent ε a₀
      (by norm_num) hθ hθ1 hα hβ0 hγ hreg hε hεsmall
  let r := carrierScale A D ε
  let h := coarseScale A D γ.exponent s ε
  let t := jitterScale A D γ.exponent s ε
  let ℓ := roughScale A D γ.exponent s ε
  let N := fun n => carrierDegreeWeight R₀ ((D : ℝ) * budget.multiplierLoss) (t n)
  let τ := fun n => carrierTaper budget.taperGap (t n)
  let δ := normalizedCarrierBound (Q.choose 2) (4 * Q) C₀ R₀ (jitterExponent A D γ.exponent s ε)
    budget.taperGap ((D : ℝ) * budget.multiplierLoss)
  let M := propensityWitnessSymbolConstant d Q N₀ θ K₀
  let CF := propensityLocalFineConstant Q D c N₀ M θ κ
  let CC := propensityLocalCrudeConstant Q D c N₀ θ κ
  let B := (designDensityCeiling d θ : ℝ)
  let CG := globalGhostConstant d q θ budget.volumeExponent
  let CP := sharedClusterProbabilityConstant d Q θ
  let envelope := propensityRateEnvelope D CF CC B CG CP A γ.exponent s ε (a₀ * a₀)
    budget.volumeExponent budget.taperGap
  have henv : Tendsto envelope atTop (𝓝 0) := propensityRateEnvelope_tendsto D CF CC B CG CP
    A γ.exponent s ε (a₀ * a₀) hA hD hγ hs hε budget
  have hp := (concrete_scale_exponents A D γ.exponent s ε hA hD hγ hs hreg hε hεsmall).2.2
  have hsmalllim : Tendsto (fun n => a₀ * t n ^ α.exponent * (1 + N₀)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((jitterPower_tendsto (jitterExponent A D γ.exponent s ε) α.exponent hp hα).const_mul a₀).mul_const (1 + N₀)
  refine ⟨a₀ * a₀ / 4, by positivity, ?_⟩
  filter_upwards [hcarrier, hδlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    henv.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    hsmalllim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hcn hδn henvn hsmalln
  obtain ⟨w, hw, hw2, hwlo, hwhi, hN, hm, hcarr⟩ := hcn
  have hb := scales_balanced A D γ.exponent s ε hA hD hγ hs hreg hε hεsmall n
  have hl := roughScale_bounds A D γ.exponent s ε hA hD hγ hs hreg hε hεsmall n
  have hbal := roughPropensity_scale_balance α.exponent β.exponent D γ.exponent ε
    hα hβ0 hαβ hD hγ hreg hε hεsmall n
  have hr1 : r n ≤ 1 := hb.2.1.trans hb.2.2.1
  have hℓh : ℓ n ≤ h n := hl.2.trans hb.2.1
  have hℓt : ℓ n ≤ t n := mul_le_of_le_one_right hb.2.2.2.1.le hr1
  let ja := a₀ * ℓ n ^ α.exponent
  let b := a₀ * r n ^ β.exponent
  have hja : 0 ≤ ja := mul_nonneg ha₀.le (Real.rpow_nonneg hl.1.le _)
  have hb0 : 0 ≤ b := mul_nonneg ha₀.le (Real.rpow_nonneg hb.1.le _)
  have hba : b ≤ a₀ := mul_le_of_le_one_right ha₀.le (Real.rpow_le_one hb.1.le hr1 hβ0.le)
  have hsmall : ja * (1 + N₀) ≤ 1 := by
    apply le_trans _ hsmalln.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hl.1.le hℓt hα.le) ha₀.le) (by positivity)
  have hbtja : b * t n ≤ ja := mixed_propensity_effective_shift_le a₀ a₀ (r n) (t n)
    α.exponent β.exponent ha₀.le le_rfl hb.1 hr1 hb.2.2.2.1 hb.2.2.2.2.1 hα1 hαβ
  have hlegal (T : Finset (d → ℤ)) side ζ (ξ : T → MomentGrid (CoefficientExponent d Q) (4 * Q)) :
      (roughPropensityFields side T (fun k => paperCoefficientAtoms Q 1 (extendBlockSample T ξ k))
        x₀ (ℓ n) (r n) (h n) ja b (t n) ζ).Legal α β γ Lπ L₀ Lτ κ :=
    hmodels a₀ ha₀.le haL side T (extendBlockSample T ξ) x₀ (ℓ n) (r n) (h n) (t n)
      hl.1 hl.2 hb.2.1 hb.2.2.1 hb.2.2.2.1.le hb.2.2.2.2.1 hbal ζ
  obtain ⟨W, hW⟩ := exists_boundedPropensityMomentWitness_family Q 1 (activeBlocks (r n) (h n))
    x₀ (ℓ n) (r n) (h n) hl.1.le hb.1 c w (N n) N₀ θ ja (t n) (τ n) K₀ (δ n)
    hc hN₀ hθ.le hK₀.le hδn.le (hcarr x₀)
  have hamp : ja * b * t n = (a₀ * a₀) * signalScale A D γ.exponent s ε n := by
    have he := hbal.trans (coarseScale_power A D γ.exponent s ε hγ.ne' n)
    calc
      _ = (a₀ * a₀) * (ℓ n ^ α.exponent * r n ^ β.exponent * t n) := by dsimp only [ja, b]; ring
      _ = _ := by rw [he]
  have hwn : w ≤ t n ^ D := hwhi.trans (by have := pow_nonneg hb.2.2.2.1.le D; linarith)
  have hnum := propensity_numeric_bound_le_envelope D CF CC B CG CP A γ.exponent s ε (a₀ * a₀)
    budget.volumeExponent budget.taperGap hA hD hγ hs hreg hε hεsmall
    (propensityLocalFineConstant_nonneg Q D c N₀ M θ κ)
    (propensityLocalCrudeConstant_nonneg Q D c N₀ θ κ) (NNReal.coe_nonneg _) n w hwn
  dsimp only at hnum
  rw [← hQorder] at hnum
  have hnr : ((n + 1 : ℕ) : ℝ) * r n ^ D ≤ 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      carrierScale_sparse D (Fintype.card_pos (α := d)) A ε hA hε.le n
  let H₀ : DiscreteLaw ℕ := DiscreteLaw.ofPMF (PMF.pure 0)
  have hfinal : ENNReal.ofReal (ja * b * t n / 4) ≤
      minimaxRisk α β γ Lπ L₀ Lτ κ lower upper hκ.le x₀ (n + 1) := by
    apply propensity_witness_minimax_of_numeric_bound H₀ q 1 x₀ (ℓ n) (r n) (h n) c w (N n) N₀ θ
      ja b (t n) (τ n) K₀ (δ n) M budget.volumeExponent hl.1 hb.1 hl.2 hb.2.1 hw (by linarith)
      hc hN₀ hN hθ.le hθ1 budget.volume_pos budget.volume_lt (carrierTaper_pos _ _ hb.2.2.2.1)
      (fun z => (hm z).1) (fun z => (hm z).2) (hrough x₀ (ℓ n) (h n) hl.1 hℓh)
      hja hsmall hb0 (hba.trans ha1) hb.2.2.2.1.le hbtja
      (propensityWitnessSymbolConstant_nonneg Q N₀ θ K₀ hN₀ hθ.le hK₀.le)
      (hcarr x₀) W hW hlegal hκ hθlo hθhi (n + 1) hnr
      (fun T ξ x => hsmooth b hb0 (hba.trans haS) T ξ x₀ (r n) hb.1 x)
    rw [hamp]
    simpa only [Nat.cast_add, Nat.cast_one] using hnum.trans henvn.le
  rw [hamp] at hfinal
  convert hfinal using 1
  congr 1
  ring

end CausalLowerbound.PartC

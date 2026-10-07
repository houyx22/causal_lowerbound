import CausalLowerbound.PartB.PaperLegalFamily
import CausalLowerbound.PartB.GlobalComparisonRates

/-! Actual polynomial-scale experiments have total variation tending to
zero. The positive carriers are selected from the constructive theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open MeasureTheory Filter
open scoped Topology Classical
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def paperComparisonBound (Q : ℕ) (A γ ε θ B c κ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (n : ℕ) : ℝ :=
  let D := (Fintype.card d : ℝ)
  let r := paperFineScale A D ε n
  let h := paperCoarseScale A D γ ε n
  let μ := mixedDesignExperiment Q (activeBlocks r h) θ hθ hθ1 H kernel x₀ r (n + 1)
  μ.real (largeClusterEvent (n + 1) Q x₀ r h) + Real.sqrt
    (uniformInformationConstant κ Q * (c * c) ^ 2 * paperSignalScale A D γ ε n ^ 2 *
      ∫ x : Fin (n + 1) → d → ℝ,
        globalGhostCost H Q θ (logarithmicThreshold (jitterExponent A D γ ε) B ((n : ℝ) + 1)) x₀ r h x ∂μ)

theorem paper_actual_totalVariation_tendsto [Nonempty d] (Q : ℕ) [NeZero Q] (ρ : ℝ)
    (α β γ : Regularity) (ε c θ B : ℝ) (x₀ : d → ℝ)
    (hρ : 0 < ρ) (hA : 0 < α.exponent + β.exponent) (hγ : 0 < γ.exponent)
    (hreg : (α.exponent + β.exponent) * (2 + (Fintype.card d : ℝ) / γ.exponent) < Fintype.card d)
    (hε : 0 < ε) (hεsmall : ε < γ.exponent / Fintype.card d - rateExponent (α.exponent + β.exponent) (Fintype.card d) γ.exponent)
    (hc : 0 < c) (hc1 : c ≤ 1 / 2) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B)
    (hQ : Q = matchingOrder (Fintype.card d) γ.exponent
      (rateExponent (α.exponent + β.exponent) (Fintype.card d) γ.exponent + ε)
      ((Fintype.card d : ℝ) * ε / (2 * (α.exponent + β.exponent))))
    (Lπ L₀ Lτ κ : ℝ) (hκ : 0 < κ)
    (hlegal : PaperLegalFamily Q ρ α β γ ε c x₀ Lπ L₀ Lτ κ) :
    ∃ (H : ℕ → DiscreteLaw ℕ)
      (kernel : ℕ → ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))),
      (∀ᶠ n in atTop, 0 < (H n).weight 0 ∧ ∀ label z, 0 < (kernel n label).weight z) ∧
      Tendsto (fun n =>
        (paperComparisonDensity Q ρ α β γ ε c θ hθ.le hθ1 x₀ Lπ L₀ Lτ κ hκ.le hlegal (H n) (kernel n) n true).totalVariation
          (paperComparisonDensity Q ρ α β γ ε c θ hθ.le hθ1 x₀ Lπ L₀ Lτ κ hκ.le hlegal (H n) (kernel n) n false))
        atTop (𝓝 0) := by
  let A := α.exponent + β.exponent
  let D := (Fintype.card d : ℝ)
  let p := jitterExponent A D γ.exponent ε
  have hD : 0 < D := by dsimp only [D]; exact_mod_cast (Fintype.card_pos (α := d))
  have hp : 0 < p := (concrete_scale_exponents A D γ.exponent ε hA hD hγ hreg hε hεsmall).2.2
  let Pair := DiscreteLaw ℕ × (ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
  let Good := fun (n : ℕ) (z : Pair) => 0 < z.1.weight 0 ∧ (∀ label w, 0 < (z.2 label).weight w) ∧
    (paperComparisonDensity Q ρ α β γ ε c θ hθ.le hθ1 x₀ Lπ L₀ Lτ κ hκ.le hlegal z.1 z.2 n true).totalVariation
      (paperComparisonDensity Q ρ α β γ ε c θ hθ.le hθ1 x₀ Lπ L₀ Lτ κ hκ.le hlegal z.1 z.2 n false) ≤
        paperComparisonBound Q A γ.exponent ε θ B c κ hθ.le hθ1 x₀ z.1 z.2 n
  have hex : ∀ᶠ n : ℕ in atTop, ∃ z : Pair, Good n z := by
    filter_upwards [paper_uniform_global_hellinger (d := d) Q ρ θ p B hρ hθ hθ1 hp hB] with n hn
    obtain ⟨H, kernel, h0, hk, hh⟩ := hn
    have hs := paper_scales_balanced α.exponent β.exponent D γ.exponent ε hA hD hγ hreg hε hεsmall n
    have ha := paper_amplitude_bounds α.exponent β.exponent D γ.exponent ε c c α.exponent_nonneg β.exponent_nonneg
      hA hD hγ hreg hε hεsmall hc hc1 hc hc1 n
    let r := paperFineScale A D ε n
    let h := paperCoarseScale A D γ.exponent ε n
    let t := paperJitterScale A D γ.exponent ε n
    let a := c * r ^ α.exponent
    let b := c * r ^ β.exponent
    have hl := hh x₀ r h a b hs.1 (hs.1.trans_le hs.2.1) hs.2.1 ha.1 ha.2.1 ha.2.2.1 ha.2.2.2
      α β γ Lπ L₀ Lτ κ hκ (hlegal n) (n + 1)
    have hb := physicalComparison_totalVariation_le Q ρ H kernel θ
      (logarithmicThreshold p B ((n : ℝ) + 1)) hθ.le hθ1 x₀ r h a b t hs.1 hκ (hlegal n) (n + 1) hl
    refine ⟨⟨H, kernel⟩, h0, hk, ?_⟩
    change _ ≤ paperComparisonBound Q A γ.exponent ε θ B c κ hθ.le hθ1 x₀ H kernel n
    apply hb.trans_eq
    dsimp only [paperComparisonBound]
    congr 2
    have hbal := paper_target_balance α.exponent β.exponent D γ.exponent ε c c
      hA hD hγ hreg hε hεsmall n
    change a * b * t ^ 2 = c * c * paperSignalScale A D γ.exponent ε n at hbal
    rw [hbal]
    ring
  let fallback : Pair := ⟨DiscreteLaw.ofPMF (PMF.pure 0), fun _ => paperCoefficientLaw Q⟩
  let z : ℕ → Pair := fun n => if hn : ∃ v : Pair, Good n v then hn.choose else fallback
  have hz : ∀ᶠ n in atTop, Good n (z n) := by
    filter_upwards [hex] with n hn
    dsimp only [z]
    rw [dif_pos hn]
    exact hn.choose_spec
  refine ⟨fun n => (z n).1, fun n => (z n).2, hz.mono (fun n hn => ⟨hn.1, hn.2.1⟩), ?_⟩
  have hb := paper_globalComparison_bound_tendsto A γ.exponent ε θ (uniformInformationConstant κ Q * (c * c) ^ 2)
    hA hγ hε hθ.le hθ1 hreg hεsmall B (fun n => (z n).1) (fun n => (z n).2) x₀
  dsimp only at hb
  rw [← hQ] at hb
  exact squeeze_zero' (Filter.Eventually.of_forall (fun n => DensityLaw.totalVariation_nonneg _ _))
    (hz.mono (fun n hn => hn.2.2)) hb

end CausalLowerbound.PartB.ShellGeometry

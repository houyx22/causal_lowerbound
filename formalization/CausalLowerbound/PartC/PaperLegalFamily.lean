import CausalLowerbound.PartC.MixedModelLegality
import CausalLowerbound.PartC.MixedScaleBalance

/-! One fixed amplitude makes every member of the actual mixed family
legal at the concrete rate scales, uniformly in all signs and coefficients. -/
noncomputable section
set_option autoImplicit false
namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

def RoughPropensityLegalFamily {Q : ℕ} (U : Ω → CoefficientExponent d Q → ℝ)
    (α β γ : Regularity) (ε c : ℝ) (x₀ : d → ℝ) (Lπ L₀ Lτ κ : ℝ) : Prop :=
  let A := α.exponent + β.exponent
  let D := (Fintype.card d : ℝ)
  let s := effectiveSmoothness α.exponent β.exponent
  ∀ (n : ℕ) (side : Bool) (sample : (d → ℤ) → Ω),
    let r := carrierScale A D ε n
    let h := coarseScale A D γ.exponent s ε n
    let t := jitterScale A D γ.exponent s ε n
    let ℓ := roughScale A D γ.exponent s ε n
    ∀ ζ : activeBlocks (d := d) ℓ h → Bool,
      (roughPropensityFields side (activeBlocks r h) (fun k => U (sample k)) x₀ ℓ r h
        (c * ℓ ^ α.exponent) (c * r ^ β.exponent) t ζ).Legal α β γ Lπ L₀ Lτ κ

def RoughOutcomeLegalFamily {Q : ℕ} (U : Ω → CoefficientExponent d Q → ℝ)
    (α β γ : Regularity) (ε c : ℝ) (x₀ : d → ℝ) (Lπ L₀ Lτ κ : ℝ) : Prop :=
  let A := α.exponent + β.exponent
  let D := (Fintype.card d : ℝ)
  let s := effectiveSmoothness α.exponent β.exponent
  ∀ (n : ℕ) (side : Bool) (sample : (d → ℤ) → Ω),
    let r := carrierScale A D ε n
    let h := coarseScale A D γ.exponent s ε n
    let t := jitterScale A D γ.exponent s ε n
    let ℓ := roughScale A D γ.exponent s ε n
    ∀ ζ : activeBlocks (d := d) ℓ h → Bool,
      (roughOutcomeFields side (activeBlocks r h) (fun k => U (sample k)) x₀ ℓ r h
        (c * r ^ α.exponent) (c * ℓ ^ β.exponent) t ζ).Legal α β γ Lπ L₀ Lτ κ

theorem exists_roughPropensity_legal_family [Nonempty d] {Q : ℕ}
    (U : Ω → CoefficientExponent d Q → ℝ) (α β γ : Regularity) (ε : ℝ) (x₀ : d → ℝ)
    (hα : 0 < α.exponent) (hβ : 0 < β.exponent) (hαβ : α.exponent ≤ β.exponent)
    (hγ : 0 < γ.exponent)
    (hreg : (α.exponent + β.exponent) * (2 + (Fintype.card d : ℝ) / γ.exponent) < Fintype.card d)
    (hε : 0 < ε) (hεsmall : ε < γ.exponent / Fintype.card d -
      rateExponent (α.exponent + β.exponent) (Fintype.card d) γ.exponent (effectiveSmoothness α.exponent β.exponent))
    (Lπ L₀ Lτ κ : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀)
    (hLτ : 0 < Lτ) (hκ : κ < 1 / 4) :
    ∃ c > 0, c ≤ 1 / 2 ∧ RoughPropensityLegalFamily U α β γ ε c x₀ Lπ L₀ Lτ κ := by
  have hD : 0 < (Fintype.card d : ℝ) := by exact_mod_cast (Fintype.card_pos (α := d))
  have hs := effectiveSmoothness_pos _ _ hα hβ
  obtain ⟨e, he, he1, hl⟩ := exists_roughPropensity_legal_amplitude U α β γ
    Lπ L₀ Lτ κ hLπ hL₀ hLτ hκ
  refine ⟨e / 2, by positivity, by linarith, ?_⟩
  dsimp only [RoughPropensityLegalFamily]
  intro n side sample ζ
  have hb := scales_balanced _ _ _ _ ε (add_pos hα hβ) hD hγ hs hreg hε hεsmall n
  have hr := roughScale_bounds _ _ _ _ ε (add_pos hα hβ) hD hγ hs hreg hε hεsmall n
  have hbal := roughPropensity_scale_balance _ _ _ _ ε hα hβ hαβ hD hγ hreg hε hεsmall n
  exact hl (e / 2) (by positivity) (by linarith) side _ sample x₀ _ _ _ _
    hr.1 hr.2 hb.2.1 hb.2.2.1 hb.2.2.2.1.le hb.2.2.2.2.1 hbal ζ

theorem exists_roughOutcome_legal_family [Nonempty d] {Q : ℕ}
    (U : Ω → CoefficientExponent d Q → ℝ) (α β γ : Regularity) (ε : ℝ) (x₀ : d → ℝ)
    (hα : 0 < α.exponent) (hβ : 0 < β.exponent) (hβα : β.exponent ≤ α.exponent)
    (hγ : 0 < γ.exponent)
    (hreg : (α.exponent + β.exponent) * (2 + (Fintype.card d : ℝ) / γ.exponent) < Fintype.card d)
    (hε : 0 < ε) (hεsmall : ε < γ.exponent / Fintype.card d -
      rateExponent (α.exponent + β.exponent) (Fintype.card d) γ.exponent (effectiveSmoothness α.exponent β.exponent))
    (Lπ L₀ Lτ κ : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀)
    (hLτ : 0 < Lτ) (hκ : κ < 1 / 4) :
    ∃ c > 0, c ≤ 1 / 2 ∧ RoughOutcomeLegalFamily U α β γ ε c x₀ Lπ L₀ Lτ κ := by
  have hD : 0 < (Fintype.card d : ℝ) := by exact_mod_cast (Fintype.card_pos (α := d))
  have hs := effectiveSmoothness_pos _ _ hα hβ
  obtain ⟨e, he, he1, hl⟩ := exists_roughOutcome_legal_amplitude U α β γ
    Lπ L₀ Lτ κ hLπ hL₀ hLτ hκ
  refine ⟨e / 2, by positivity, by linarith, ?_⟩
  dsimp only [RoughOutcomeLegalFamily]
  intro n side sample ζ
  have hb := scales_balanced _ _ _ _ ε (add_pos hα hβ) hD hγ hs hreg hε hεsmall n
  have hr := roughScale_bounds _ _ _ _ ε (add_pos hα hβ) hD hγ hs hreg hε hεsmall n
  have hbal := roughOutcome_scale_balance _ _ _ _ ε hα hβ hβα hD hγ hreg hε hεsmall n
  exact hl (e / 2) (by positivity) (by linarith) side _ sample x₀ _ _ _ _
    hr.1 hr.2 hb.2.1 hb.2.2.1 hb.2.2.2.1.le hb.2.2.2.2.1 hbal ζ

end CausalLowerbound.PartC

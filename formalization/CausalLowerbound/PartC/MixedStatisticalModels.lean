import CausalLowerbound.PartC.CarrierDesign
import CausalLowerbound.PartC.MixedModels
import CausalLowerbound.PartB.StatisticalModel

/-! Both mixed parameter families are members of the original statistical
model class, with the normalized shared-sign carrier design. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Inhabited Ω]
  {θ : ℝ} {α β γ : Regularity} {Lπ L₀ Lτ κ lower upper : ℝ}

theorem CarrierProfile.designLegal (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hlo : lower ≤ (1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d))
    (hhi : (1 + θ) ^ (5 ^ Fintype.card d) / (1 - θ) ^ (5 ^ Fintype.card d) ≤ upper)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) :
    DesignLegal lower upper (F.normalized S x₀ r) := by
  have hd := F.normalized_legal hθ hθ1 S x₀ r
  exact ⟨hd.1, hd.2.1, fun x => ⟨hlo.trans (hd.2.2 x).1, (hd.2.2 x).2.trans hhi⟩⟩

def roughPropensityStatisticalModel {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (coeff : S → Ω)
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hlegal : (roughPropensityFields side S (fun k => atoms (extendBlockSample S coeff k))
      x₀ ℓ r h ja b t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hd : DesignLegal lower upper (F.normalized S x₀ r)) :
    StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper where
  fields := roughPropensityFields side S (fun k => atoms (extendBlockSample S coeff k))
    x₀ ℓ r h ja b t ζ
  design := F.normalized S x₀ r
  legal := ⟨hlegal, hd⟩
  regular := by
    have hs := roughPropensityFields_smooth side S (fun k => atoms (extendBlockSample S coeff k))
      x₀ ℓ r h ja b t ζ
    exact ⟨hs.1.of_le (WithTop.coe_le_coe.mpr le_top),
      hs.2.1.of_le (WithTop.coe_le_coe.mpr le_top), hs.2.2.of_le (WithTop.coe_le_coe.mpr le_top)⟩
  design_nonneg := F.normalized_nonneg hθ hθ1 S x₀ r

def roughOutcomeStatisticalModel {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (coeff : S → Ω)
    (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hlegal : (roughOutcomeFields side S (fun k => atoms (extendBlockSample S coeff k))
      x₀ ℓ r h a jb t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hd : DesignLegal lower upper (F.normalized S x₀ r)) :
    StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper where
  fields := roughOutcomeFields side S (fun k => atoms (extendBlockSample S coeff k))
    x₀ ℓ r h a jb t ζ
  design := F.normalized S x₀ r
  legal := ⟨hlegal, hd⟩
  regular := by
    have hs := roughOutcomeFields_smooth side S (fun k => atoms (extendBlockSample S coeff k))
      x₀ ℓ r h a jb t ζ
    exact ⟨hs.1.of_le (WithTop.coe_le_coe.mpr le_top),
      hs.2.1.of_le (WithTop.coe_le_coe.mpr le_top), hs.2.2.of_le (WithTop.coe_le_coe.mpr le_top)⟩
  design_nonneg := F.normalized_nonneg hθ hθ1 S x₀ r

theorem roughPropensityStatisticalModel_center {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (coeff : S → Ω)
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hlegal : (roughPropensityFields side S (fun k => atoms (extendBlockSample S coeff k))
      x₀ ℓ r h ja b t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hd : DesignLegal lower upper (F.normalized S x₀ r)) :
    (roughPropensityStatisticalModel side S atoms coeff x₀ ℓ r h ja b t ζ F hθ hθ1 hlegal hd).fields.effect x₀ =
      if side then ja * b * t else 0 :=
  roughPropensityFields_effect_center side S _ x₀ ℓ r h ja b t ζ

theorem roughOutcomeStatisticalModel_center {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (coeff : S → Ω)
    (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hlegal : (roughOutcomeFields side S (fun k => atoms (extendBlockSample S coeff k))
      x₀ ℓ r h a jb t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hd : DesignLegal lower upper (F.normalized S x₀ r)) :
    (roughOutcomeStatisticalModel side S atoms coeff x₀ ℓ r h a jb t ζ F hθ hθ1 hlegal hd).fields.effect x₀ =
      if side then a * t * jb else 0 :=
  roughOutcomeFields_effect_center side S _ x₀ ℓ r h a jb t ζ

end CausalLowerbound.PartC

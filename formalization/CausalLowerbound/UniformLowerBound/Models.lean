import CausalLowerbound.UniformLowerBound.Profiles
import CausalLowerbound.PartB.StatisticalModel

/-! The two binary experiments, with an exactly uniform covariate design.
`regime = false` selects the alpha >= beta construction, and `true` selects
beta >= alpha.  `side = true` is P; `side = false` is Q. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace CausalLowerbound.UniformLowerBound
open PartB PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def fields (regime side : Bool) (S : Finset (d → ℤ)) (ζ : (d → ℤ) → Bool)
    (x₀ : d → ℝ) (ℓ h a b : ℝ) : NuisanceFields d where
  propensity x := 1 / 2 + if side && !regime then 0 else a * signedField S ζ x₀ ℓ h x
  baseline x := 1 / 2 + (if side && regime then 0 else b * signedField S ζ x₀ ℓ h x) -
    if side then targetField x₀ h (4 * a * b) x / 2 else 0
  effect x := if side then targetField x₀ h (4 * a * b) x else 0

theorem fields_smooth (regime side : Bool) (S : Finset (d → ℤ))
    (ζ : (d → ℤ) → Bool) (x₀ : d → ℝ) (ℓ h a b : ℝ) :
    ContDiff ℝ ∞ (fields regime side S ζ x₀ ℓ h a b).propensity ∧
    ContDiff ℝ ∞ (fields regime side S ζ x₀ ℓ h a b).baseline ∧
    ContDiff ℝ ∞ (fields regime side S ζ x₀ ℓ h a b).effect := by
  have hU := signedField_smooth S ζ x₀ ℓ h
  have hT := targetField_smooth x₀ h (4 * a * b)
  cases regime <;> cases side <;> simp only [fields, Bool.false_eq_true, Bool.and_false,
    Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, Bool.and_true,
    ↓reduceIte, add_zero, sub_zero] <;>
    refine ⟨?_, ?_, ?_⟩
  all_goals first
    | exact hT
    | exact contDiff_const
    | exact contDiff_const.add (contDiff_const.mul hU)
    | exact (contDiff_const.add (contDiff_const.mul hU)).sub (hT.div_const 2)
    | exact contDiff_const.sub (hT.div_const 2)

theorem fields_separation (regime : Bool) (S : Finset (d → ℤ))
    (ζP ζQ : (d → ℤ) → Bool) (x₀ : d → ℝ) (ℓ h a b : ℝ) :
    (fields regime true S ζP x₀ ℓ h a b).effect x₀ -
      (fields regime false S ζQ x₀ ℓ h a b).effect x₀ = 4 * a * b := by
  simp [fields, targetField_center]

theorem uniformDesign_legal (lower upper : ℝ) (hl : lower ≤ 1) (hu : 1 ≤ upper) :
    DesignLegal (d := d) lower upper (fun _ => 1) := by
  refine ⟨measurable_const, ?_, fun _ => ⟨hl, hu⟩⟩
  simp

def uniformStatisticalModel (regime side : Bool) (S : Finset (d → ℤ))
    (ζ : (d → ℤ) → Bool) (x₀ : d → ℝ) (ℓ h a b : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ lower upper : ℝ}
    (hlegal : (fields regime side S ζ x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ)
    (hl : lower ≤ 1) (hu : 1 ≤ upper) :
    StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper where
  fields := fields regime side S ζ x₀ ℓ h a b
  design := fun _ => 1
  legal := ⟨hlegal, uniformDesign_legal lower upper hl hu⟩
  regular := by
    have hs := fields_smooth regime side S ζ x₀ ℓ h a b
    exact ⟨hs.1.of_le (WithTop.coe_le_coe.mpr le_top),
      hs.2.1.of_le (WithTop.coe_le_coe.mpr le_top),
      hs.2.2.of_le (WithTop.coe_le_coe.mpr le_top)⟩
  design_nonneg _ := zero_le_one

@[simp] theorem uniformStatisticalModel_design (regime side : Bool) (S : Finset (d → ℤ))
    (ζ : (d → ℤ) → Bool) (x₀ : d → ℝ) (ℓ h a b : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ lower upper : ℝ}
    (hlegal : (fields regime side S ζ x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ)
    (hl : lower ≤ 1) (hu : 1 ≤ upper) :
    (uniformStatisticalModel regime side S ζ x₀ ℓ h a b hlegal hl hu).design = fun _ => 1 := rfl

end CausalLowerbound.UniformLowerBound

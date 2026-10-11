import CausalLowerbound.UniformLowerBound.Models
import CausalLowerbound.UniformLowerBound.LocalComparison

/-! The polynomial likelihoods are the actual conditional binary laws. -/
noncomputable section
set_option autoImplicit false
namespace CausalLowerbound.UniformLowerBound
open PartB PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem conditionalLaw_weight_eq (regime side : Bool) (S : Finset (d → ℤ))
    (ζ : (d → ℤ) → Bool) (x₀ : d → ℝ) (ℓ h a b : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : (fields regime side S ζ x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (x : d → ℝ) (w : Bool × Bool) :
    ((fields regime side S ζ x₀ ℓ h a b).conditionalLaw hlegal hκ x).weight w =
      (if side then likelihoodP regime a b (sign w.1) (sign w.2)
        (signedField S ζ x₀ ℓ h x) (coarseBump x₀ h x ^ 2)
       else likelihoodQ a b (sign w.1) (sign w.2) (signedField S ζ x₀ ℓ h x)) / 4 := by
  obtain ⟨r, t⟩ := w
  rw [NuisanceFields.conditionalLaw_cell]
  cases regime <;> cases side <;> cases r <;> cases t <;>
    simp only [fields, likelihoodP, likelihoodP1, likelihoodP2, likelihoodQ,
      targetField, sign, Bool.false_eq_true, Bool.and_false, Bool.false_and,
      Bool.true_and, Bool.not_false, Bool.not_true, Bool.and_true, ↓reduceIte] <;> ring

theorem conditionalLaw_cell_lower (F : NuisanceFields d) {α β γ : Regularity}
    {Lπ L₀ Lτ κ : ℝ} (hlegal : F.Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (x : d → ℝ) (w : Bool × Bool) :
    κ ^ 2 ≤ (F.conditionalLaw hlegal hκ x).weight w := by
  obtain ⟨r, t⟩ := w
  obtain ⟨hp0, hp1, hm0, hm1, ht0, ht1⟩ := hlegal.2.2.2 x
  have hA : κ ≤ if r then F.propensity x else 1 - F.propensity x := by
    cases r <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have hY : κ ≤ if t then F.baseline x + (if r then F.effect x else 0)
      else 1 - (F.baseline x + (if r then F.effect x else 0)) := by
    cases r <;> cases t <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero] <;> linarith
  rw [NuisanceFields.conditionalLaw_cell]
  simpa only [pow_two] using mul_le_mul hA hY hκ (hκ.trans hA)

end CausalLowerbound.UniformLowerBound

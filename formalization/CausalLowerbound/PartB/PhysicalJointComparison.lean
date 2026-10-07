import CausalLowerbound.PartB.ConditionalMeasurability
import CausalLowerbound.PartB.PhysicalGlobalHellinger
import CausalLowerbound.CommonMarginalTesting

/-! Joint laws on the actual covariates and binary outcomes, with their
common mixed design marginal and measurable conditional densities. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω] [Inhabited Ω]

def physicalComparisonConditional {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (μ₀ : FiniteLaw Ω)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {n : ℕ} (x : Fin n → d → ℝ) : FiniteLaw (Fin n → Bool × Bool) :=
  finitePhysicalConditional side S atoms x₀ r h a b t δ
    (if side then (fun _ => μ₀) else physicalCoefficientPosteriors H kernel Q S θ hθ hθ1 x₀ r x) hlegal hκ x

theorem physicalComparisonConditional_measurable {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (μ₀ : FiniteLaw Ω)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (n : ℕ) (w : Fin n → Bool × Bool) :
    Measurable (fun x => (physicalComparisonConditional side S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ hlegal hκ x).weight w) := by
  apply finitePhysicalConditional_measurable
  intro k z
  cases side with
  | false => exact physicalCoefficientPosteriors_measurable H kernel Q S θ hθ hθ1 x₀ r n k z
  | true => simpa only [if_pos rfl] using
      (measurable_const : Measurable (fun _ : Fin n → d → ℝ => μ₀.weight z))

def physicalComparisonDensity {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (μ₀ : FiniteLaw Ω)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (n : ℕ) :
    DensityLaw ((mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n).prod
      (Measure.count : Measure (Fin n → Bool × Bool))) := by
  letI := mixedDesignExperiment_probability Q S θ hθ hθ1 H kernel x₀ r n
  exact conditionalDensityLaw _
    (physicalComparisonConditional side S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ hlegal hκ)
    (physicalComparisonConditional_measurable side S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ hlegal hκ n)

theorem physicalComparison_totalVariation_le (Q : ℕ) (ρ : ℝ) (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t : ℝ) (hr : 0 < r)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ} (hκ : 0 < κ)
    (hlegal : ∀ (side : Bool) (z : activeBlocks (d := d) r h → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (modelFields side (activeBlocks r h) (fun k => paperCoefficientAtoms Q ρ (extendBlockSample (activeBlocks r h) z k))
        x₀ r h a b t (a * b * t ^ 2)).Legal α β γ Lπ L₀ Lτ κ)
    (n : ℕ)
    (hhell : ∀ x : Fin n → d → ℝ, x ∉ largeClusterEvent n Q x₀ r h →
      (finitePhysicalConditional true (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
        (fun _ => paperCoefficientLaw Q) (hlegal true) hκ.le x).hellingerSq
        (finitePhysicalConditional false (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
          (physicalCoefficientPosteriors H kernel Q (activeBlocks r h) θ hθ hθ1 x₀ r x) (hlegal false) hκ.le x) ≤
          uniformInformationConstant κ Q * (a * b * t ^ 2) ^ 2 * globalGhostCost H Q θ ε x₀ r h x) :
    (physicalComparisonDensity true (activeBlocks r h) (paperCoefficientAtoms Q ρ) (paperCoefficientLaw Q)
      H kernel θ hθ hθ1 x₀ r h a b t (a * b * t ^ 2) (hlegal true) hκ.le n).totalVariation
      (physicalComparisonDensity false (activeBlocks r h) (paperCoefficientAtoms Q ρ) (paperCoefficientLaw Q)
        H kernel θ hθ hθ1 x₀ r h a b t (a * b * t ^ 2) (hlegal false) hκ.le n) ≤
      (mixedDesignExperiment Q (activeBlocks r h) θ hθ hθ1 H kernel x₀ r n).real (largeClusterEvent n Q x₀ r h) +
        Real.sqrt (uniformInformationConstant κ Q * (a * b * t ^ 2) ^ 2 *
          ∫ x : Fin n → d → ℝ, globalGhostCost H Q θ ε x₀ r h x
            ∂mixedDesignExperiment Q (activeBlocks r h) θ hθ hθ1 H kernel x₀ r n) := by
  let μ := mixedDesignExperiment Q (activeBlocks r h) θ hθ hθ1 H kernel x₀ r n
  letI := mixedDesignExperiment_probability Q (activeBlocks r h) θ hθ hθ1 H kernel x₀ r n
  let C := uniformInformationConstant κ Q * (a * b * t ^ 2) ^ 2
  let cost := fun x : Fin n → d → ℝ => C * globalGhostCost H Q θ ε x₀ r h x
  have hi : Integrable cost μ := (globalGhostCost_integrable H Q θ ε hθ hθ1 kernel x₀ r h hr n).const_mul C
  have hc (x) : 0 ≤ cost x := mul_nonneg
    (mul_nonneg (uniformInformationConstant_nonneg κ Q) (sq_nonneg _))
    (globalGhostCost_nonneg H Q θ ε hθ hθ1 x₀ r h hr x)
  have he := common_marginal_component_principle μ
    (physicalComparisonConditional true (activeBlocks r h) (paperCoefficientAtoms Q ρ) (paperCoefficientLaw Q)
      H kernel θ hθ hθ1 x₀ r h a b t (a * b * t ^ 2) (hlegal true) hκ.le)
    (physicalComparisonConditional false (activeBlocks r h) (paperCoefficientAtoms Q ρ) (paperCoefficientLaw Q)
      H kernel θ hθ hθ1 x₀ r h a b t (a * b * t ^ 2) (hlegal false) hκ.le)
    (physicalComparisonConditional_measurable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n)
    (physicalComparisonConditional_measurable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n)
    (largeClusterEvent n Q x₀ r h) (largeClusterEvent_measurable n Q x₀ r h) cost hi hhell
  apply he.trans
  apply add_le_add_left
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∫ x, cost x ∂μ := integral_mono
      (hi.indicator (largeClusterEvent_measurable n Q x₀ r h).compl) hi (fun x => by
        by_cases hx : x ∈ (largeClusterEvent n Q x₀ r h)ᶜ
        · simp only [Set.indicator_of_mem hx]; exact le_rfl
        · simp only [Set.indicator_of_not_mem hx]; exact hc x)
    _ = _ := integral_const_mul C _

end CausalLowerbound.PartB.ShellGeometry

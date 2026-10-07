import CausalLowerbound.PartB.SampleDensity

/-! Equality with the original experiment: draw labels and coefficients
from the tilted prior, then sample covariates and independent binary cells. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 120000
open MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound

theorem DiscreteLaw.mixFinite_constant {I Ω : Type*} [Fintype Ω]
    (H : DiscreteLaw I) (P : FiniteLaw Ω) : H.mixFinite (fun _ => P) = P := by
  apply FiniteLaw.ext
  intro z
  change (∑' i, H.weight i * P.weight z) = P.weight z
  rw [tsum_mul_right, H.tsum_weight, one_mul]

namespace PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω] [Inhabited Ω]

def fixedPhysicalConditional {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ} (z : S → Ω)
    (hlegal : (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {n : ℕ} (x : Fin n → d → ℝ) : FiniteLaw (Fin n → Bool × Bool) :=
  FiniteLaw.independent (fun i =>
    (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).conditionalLaw hlegal hκ (x i))

theorem fixedPhysicalConditional_weight {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ} (z : S → Ω)
    (hlegal : (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {n : ℕ} (x : Fin n → d → ℝ) (w : Fin n → Bool × Bool) :
    (fixedPhysicalConditional side S atoms x₀ r h a b t δ z hlegal hκ x).weight w =
      ∏ i, modelCellMass side S atoms x₀ r h a b t δ (x i) (w i) z := by
  simp only [fixedPhysicalConditional, FiniteLaw.independent]
  apply Finset.prod_congr rfl
  intro i _
  exact (modelCellMass_eq_conditional side S atoms x₀ r h a b t δ (x i) (w i) z hlegal hκ).symm

theorem fixedPhysicalConditional_measurable {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ} (z : S → Ω)
    (hlegal : (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (n : ℕ) (w : Fin n → Bool × Bool) :
    Measurable (fun x => (fixedPhysicalConditional side S atoms x₀ r h a b t δ z hlegal hκ x).weight w) := by
  simp only [fixedPhysicalConditional, FiniteLaw.independent]
  exact Finset.measurable_prod Finset.univ (fun i _ =>
    ((NuisanceFields.conditionalLaw_measurable _ hlegal hκ
      (modelFields_measurable side S _ x₀ r h a b t δ)) (w i)).comp (measurable_pi_apply i))

def physicalPriorExperiment {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (n : ℕ) : Measure ((Fin n → d → ℝ) × (Fin n → Bool × Bool)) :=
  (tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r n).mixMeasures (fun z =>
    conditionalExperiment (designSampleMeasure Q S θ z.1 x₀ r n)
      (fixedPhysicalConditional side S atoms x₀ r h a b t δ z.2 (hlegal z.2) hκ))

theorem physicalPosteriorExperiment_eq_mixture {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (n : ℕ) :
    conditionalExperiment (mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n)
      (fun x => finitePhysicalConditional side S atoms x₀ r h a b t δ
        (physicalCoefficientPosteriors H kernel Q S θ hθ hθ1 x₀ r x) hlegal hκ x) =
      physicalPriorExperiment side S atoms H kernel θ hθ hθ1 x₀ r h a b t δ hlegal hκ n := by
  let π := tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r n
  let μ := Measure.pi (fun _ : Fin n => cubeMeasure d)
  let f := fun z : (S → ℕ) × (S → Ω) => designSampleDensity Q S θ z.1 x₀ r (n := n)
  let L := fun z : (S → ℕ) × (S → Ω) =>
    fixedPhysicalConditional side S atoms x₀ r h a b t δ z.2 (hlegal z.2) hκ (n := n)
  let K := fun x : Fin n → d → ℝ => finitePhysicalConditional side S atoms x₀ r h a b t δ
    (physicalCoefficientPosteriors H kernel Q S θ hθ hθ1 x₀ r x) hlegal hκ x
  have hBayes (x : Fin n → d → ℝ) (w : Fin n → Bool × Bool) :
      (K x).weight w = π.expect (fun z => f z x * (L z x).weight w) / π.expect (fun z => f z x) := by
    dsimp only [K, L, f, π]
    simp_rw [fixedPhysicalConditional_weight]
    change _ = (tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r n).expect
      (fun z => (∏ i, normalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) *
        ∏ i, modelCellMass side S atoms x₀ r h a b t δ (x i) (w i) z.2) /
      (tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r n).expect
        (fun z => ∏ i, normalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i))
    rw [designPosterior_Bayes,
      designPosterior_coefficient_expect H kernel Q S θ hθ hθ1 x₀ r x
        (fun z => ∏ i, modelCellMass side S atoms x₀ r h a b t δ (x i) (w i) z),
      finitePhysicalConditional_weight]
    rfl
  have he := DiscreteLaw.conditional_mixture π μ f
    (((1 + θ) ^ (5 ^ Fintype.card d) / (1 - θ) ^ (5 ^ Fintype.card d)) ^ n)
    (fun z => designSampleDensity_measurable Q S θ hθ hθ1 z.1 x₀ r n)
    (fun z x => (designSampleDensity_pos Q S θ hθ hθ1 z.1 x₀ r x).le)
    (fun z x => (designSampleDensity_bounds Q S θ hθ hθ1 z.1 x₀ r x).2)
    L (fun z => fixedPhysicalConditional_measurable side S atoms x₀ r h a b t δ z.2 (hlegal z.2) hκ n)
    K (finitePhysicalConditional_measurable side S atoms x₀ r h a b t δ n _
      (fun k z => physicalCoefficientPosteriors_measurable H kernel Q S θ hθ hθ1 x₀ r n k z) hlegal hκ)
    (fun x => mixedDesign_density_pos Q S θ hθ hθ1 H kernel x₀ r x) hBayes
  unfold physicalPriorExperiment mixedDesignExperiment
  simp_rw [designSampleMeasure_density Q S θ hθ hθ1]
  exact he

theorem physicalCoefficientPosteriors_constant (H : DiscreteLaw ℕ) (P : FiniteLaw Ω)
    (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x₀ : d → ℝ) (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) :
    physicalCoefficientPosteriors H (fun _ => P) Q S θ hθ hθ1 x₀ r x = fun _ => P := by
  funext k
  unfold physicalCoefficientPosteriors coefficientPosterior
  exact DiscreteLaw.mixFinite_constant _ P

theorem physicalComparisonDensity_toMeasure {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (μ₀ : FiniteLaw Ω)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (n : ℕ) :
    (physicalComparisonDensity side S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ hlegal hκ n).toMeasure =
      conditionalExperiment (mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n)
        (physicalComparisonConditional side S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ hlegal hκ) := rfl

theorem physicalComparisonConditional_posterior {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (μ₀ : FiniteLaw Ω)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {n : ℕ} (x : Fin n → d → ℝ) :
    physicalComparisonConditional side S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ hlegal hκ x =
      finitePhysicalConditional side S atoms x₀ r h a b t δ
        (physicalCoefficientPosteriors H (if side then (fun _ => μ₀) else kernel) Q S θ hθ hθ1 x₀ r x) hlegal hκ x := by
  have hμ : (if side then (fun _ : S => μ₀) else physicalCoefficientPosteriors H kernel Q S θ hθ hθ1 x₀ r x) =
      physicalCoefficientPosteriors H (if side then (fun _ => μ₀) else kernel) Q S θ hθ hθ1 x₀ r x := by
    by_cases hs : side = true
    · simp only [if_pos hs, physicalCoefficientPosteriors_constant]
    · simp only [if_neg hs]
  exact congrArg (fun μ => finitePhysicalConditional side S atoms x₀ r h a b t δ μ hlegal hκ x) hμ

theorem physicalComparisonDensity_eq_mixture {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (μ₀ : FiniteLaw Ω)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (n : ℕ) :
    (physicalComparisonDensity side S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ hlegal hκ n).toMeasure =
      physicalPriorExperiment side S atoms H (if side then (fun _ => μ₀) else kernel)
        θ hθ hθ1 x₀ r h a b t δ hlegal hκ n := by
  rw [physicalComparisonDensity_toMeasure]
  let kernel' := if side then (fun _ => μ₀) else kernel
  have hμ := tiltedBlockPrior_common_Xn Q S θ hθ hθ1 H kernel kernel' x₀ r n
  have hK := funext (fun x : Fin n → d → ℝ => physicalComparisonConditional_posterior
    side S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ hlegal hκ x)
  exact (congrArg₂ conditionalExperiment hμ hK).trans
    (physicalPosteriorExperiment_eq_mixture side S atoms H kernel' θ hθ hθ1 x₀ r h a b t δ hlegal hκ n)

end PartB.ShellGeometry
end CausalLowerbound

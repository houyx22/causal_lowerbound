import CausalLowerbound.FiniteConditionalExperiment
import CausalLowerbound.PartB.LegalBinaryModels
import CausalLowerbound.PartB.DesignExperiments

/-! Actual observations (X,R,T) for the legal physical model, including
joint measurability, probability normalization, and the X marginal. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace CausalLowerbound
variable {d : Type*} [Fintype d]

theorem NuisanceFields.conditionalLaw_measurable (F : NuisanceFields d) {α β γ : Regularity}
    {Lπ L₀ Lτ κ : ℝ} (h : F.Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (hF : Measurable F.propensity ∧ Measurable F.baseline ∧ Measurable F.effect) :
    ∀ b, Measurable (fun x => (F.conditionalLaw h hκ x).weight b) := by
  intro ⟨r, t⟩
  simp_rw [F.conditionalLaw_cell h hκ]
  cases r <;> cases t <;> simp only [Bool.false_eq_true, if_false, if_true, add_zero]
  · exact (measurable_const.sub hF.1).mul (measurable_const.sub hF.2.1)
  · exact (measurable_const.sub hF.1).mul hF.2.1
  · exact hF.1.mul (measurable_const.sub (hF.2.1.add hF.2.2))
  · exact hF.1.mul (hF.2.1.add hF.2.2)

def observationMeasure (μ : Measure (d → ℝ)) (F : NuisanceFields d) {α β γ : Regularity}
    {Lπ L₀ Lτ κ : ℝ} (h : F.Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ) :
    Measure ((d → ℝ) × (Bool × Bool)) := conditionalExperiment μ (F.conditionalLaw h hκ)

theorem observationMeasure_probability (μ : Measure (d → ℝ)) [IsProbabilityMeasure μ]
    (F : NuisanceFields d) {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (h : F.Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (hF : Measurable F.propensity ∧ Measurable F.baseline ∧ Measurable F.effect) :
    IsProbabilityMeasure (observationMeasure μ F h hκ) :=
  conditionalExperiment_probability μ _ (F.conditionalLaw_measurable h hκ hF)

theorem observationMeasure_X (μ : Measure (d → ℝ)) [SFinite μ] (F : NuisanceFields d) {α β γ : Regularity}
    {Lπ L₀ Lτ κ : ℝ} (h : F.Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (hF : Measurable F.propensity ∧ Measurable F.baseline ∧ Measurable F.effect) :
    (observationMeasure μ F h hκ).map Prod.fst = μ :=
  conditionalExperiment_covariate μ _ (F.conditionalLaw_measurable h hκ hF)

theorem observationMeasure_density (μ : Measure (d → ℝ)) (f : (d → ℝ) → ℝ)
    (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) (F : NuisanceFields d)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ} (h : F.Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (hF : Measurable F.propensity ∧ Measurable F.baseline ∧ Measurable F.effect) :
    observationMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) F h hκ =
      (μ.prod Measure.count).withDensity (fun z => ENNReal.ofReal (f z.1 *
        (PartB.codedLikelihood (PartB.sign z.2.1) (PartB.sign z.2.2)
          (2 * F.propensity z.1 - 1) (2 * F.baseline z.1 - 1) (F.effect z.1) / 4))) := by
  exact conditionalExperiment_density μ f hf hn (F.conditionalLaw h hκ) (F.conditionalLaw_measurable h hκ hF)

namespace PartB.ShellGeometry
variable [DecidableEq d]

theorem modelFields_measurable {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ) :
    Measurable (modelFields side S U x₀ r h a b t δ).propensity ∧
    Measurable (modelFields side S U x₀ r h a b t δ).baseline ∧
    Measurable (modelFields side S U x₀ r h a b t δ).effect := by
  have hP := (packetField_smooth S U x₀ r h).continuous.measurable
  have hG : Measurable (fun x => coarseBump x₀ h x ^ 2) :=
    ((rescaled_smooth _ quadraticPartition_smooth x₀ h).continuous.measurable).pow_const 2
  have hη : Measurable (packetEta S x₀ r h a t) :=
    measurable_const.mul (hG.mul (measurable_const.sub (measurable_const.mul (quarticField_smooth S x₀ r).continuous.measurable)))
  have hK : Measurable (normalizedCubic S U x₀ r h a t) :=
    ((measurable_const.add hη).mul hP).sub (measurable_const.mul (hP.pow_const 3))
  have hp : Measurable (propensityPerturbation S U x₀ r h a) := measurable_const.mul hP
  have hd : Measurable (targetField x₀ h δ) := measurable_const.mul hG
  have hy : Measurable (codedOutcome side S U x₀ r h a b t δ) := by
    cases side with
    | false => exact measurable_const.mul hK
    | true => exact (measurable_const.mul hK).sub (hd.mul (measurable_const.add (measurable_const.mul hp)))
  refine ⟨(measurable_const.add hp).div_const 2, (measurable_const.add hy).div_const 2, ?_⟩
  cases side with
  | false => exact measurable_const
  | true => exact hd

end PartB.ShellGeometry
end CausalLowerbound

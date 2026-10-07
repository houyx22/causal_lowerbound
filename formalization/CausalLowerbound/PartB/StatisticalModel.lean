import CausalLowerbound.PartB.ConcreteModels
import CausalLowerbound.PartB.PhysicalJointComparison

/-! The model class and minimax absolute risk. Classical differentiability
is required in addition to derivative and fractional Holder bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 120000
open MeasureTheory
open scoped ContDiff Classical ENNReal
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem modelFields_smooth {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ) :
    ContDiff ℝ ∞ (modelFields side S U x₀ r h a b t δ).propensity ∧
    ContDiff ℝ ∞ (modelFields side S U x₀ r h a b t δ).baseline ∧
    ContDiff ℝ ∞ (modelFields side S U x₀ r h a b t δ).effect := by
  have hP := packetField_smooth S U x₀ r h
  have hG : ContDiff ℝ ∞ (fun x => coarseBump x₀ h x ^ 2) :=
    (rescaled_smooth _ quadraticPartition_smooth x₀ h).pow 2
  have hη : ContDiff ℝ ∞ (packetEta S x₀ r h a t) :=
    contDiff_const.mul (hG.mul (contDiff_const.sub (contDiff_const.mul (quarticField_smooth S x₀ r))))
  have hK : ContDiff ℝ ∞ (normalizedCubic S U x₀ r h a t) :=
    ((contDiff_const.add hη).mul hP).sub (contDiff_const.mul (hP.pow 3))
  have hp : ContDiff ℝ ∞ (propensityPerturbation S U x₀ r h a) := contDiff_const.mul hP
  have hd : ContDiff ℝ ∞ (targetField x₀ h δ) := contDiff_const.mul hG
  have hy : ContDiff ℝ ∞ (codedOutcome side S U x₀ r h a b t δ) := by
    cases side with
    | false => exact contDiff_const.mul hK
    | true => exact (contDiff_const.mul hK).sub (hd.mul (contDiff_const.add (contDiff_const.mul hp)))
  refine ⟨(contDiff_const.add hp).div_const 2, (contDiff_const.add hy).div_const 2, ?_⟩
  cases side with
  | false => exact contDiff_const
  | true => exact hd

structure StatisticalModel (d : Type*) [Fintype d] (α β γ : Regularity)
    (Lπ L₀ Lτ κ lower upper : ℝ) where
  fields : NuisanceFields d
  design : (d → ℝ) → ℝ
  legal : ModelLegal α β γ Lπ L₀ Lτ κ lower upper fields design
  regular : ContDiff ℝ α.order fields.propensity ∧
    ContDiff ℝ β.order fields.baseline ∧ ContDiff ℝ γ.order fields.effect
  design_nonneg : ∀ x, 0 ≤ design x

namespace StatisticalModel
variable {α β γ : Regularity} {Lπ L₀ Lτ κ lower upper : ℝ}

def sampleConditional (M : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hκ : 0 ≤ κ) {n : ℕ} (x : Fin n → d → ℝ) : FiniteLaw (Fin n → Bool × Bool) :=
  FiniteLaw.independent (fun i => M.fields.conditionalLaw M.legal.1 hκ (x i))

theorem sampleConditional_measurable (M : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hκ : 0 ≤ κ) (n : ℕ) (w : Fin n → Bool × Bool) :
    Measurable (fun x => (M.sampleConditional hκ x).weight w) := by
  simp only [sampleConditional, FiniteLaw.independent]
  exact Finset.measurable_prod Finset.univ (fun i _ => ((NuisanceFields.conditionalLaw_measurable _ M.legal.1 hκ
    ⟨M.regular.1.continuous.measurable, M.regular.2.1.continuous.measurable, M.regular.2.2.continuous.measurable⟩)
      (w i)).comp (measurable_pi_apply i))

def sampleMeasure (M : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper) (hκ : 0 ≤ κ) (n : ℕ) :
    Measure ((Fin n → d → ℝ) × (Fin n → Bool × Bool)) :=
  conditionalExperiment (Measure.pi (fun _ : Fin n =>
    (cubeMeasure d).withDensity (fun x => ENNReal.ofReal (M.design x)))) (M.sampleConditional hκ)

theorem sampleMeasure_probability (M : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hκ : 0 ≤ κ) (n : ℕ) : IsProbabilityMeasure (M.sampleMeasure hκ n) := by
  have hi : Integrable M.design (cubeMeasure d) := (integrable_const upper).mono'
    M.legal.2.1.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (M.design_nonneg x)]
      exact (M.legal.2.2.2 x).2))
  letI : IsProbabilityMeasure ((cubeMeasure d).withDensity (fun x => ENNReal.ofReal (M.design x))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall M.design_nonneg),
      M.legal.2.2.1, ENNReal.ofReal_one]
  exact conditionalExperiment_probability _ _ (M.sampleConditional_measurable hκ n)

def risk (M : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper) (hκ : 0 ≤ κ)
    (x₀ : d → ℝ) (n : ℕ) (est : ((Fin n → d → ℝ) × (Fin n → Bool × Bool)) → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal |est z - M.fields.effect x₀| ∂M.sampleMeasure hκ n

end StatisticalModel

def minimaxRisk (α β γ : Regularity) (Lπ L₀ Lτ κ lower upper : ℝ) (hκ : 0 ≤ κ)
    (x₀ : d → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨅ est : {f : ((Fin n → d → ℝ) × (Fin n → Bool × Bool)) → ℝ // Measurable f},
    ⨆ M : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper, M.risk hκ x₀ n est.val

def physicalStatisticalModel {Q : ℕ} {Ω : Type*} [Inhabited Ω]
    (side : Bool) (S : Finset (d → ℤ)) (atoms : Ω → CoefficientExponent d Q → ℝ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (labels : S → ℕ) (z : S → Ω)
    (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ lower upper : ℝ}
    (hlegal : (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hd : DesignLegal lower upper (normalizedDesign Q S θ (extendLabels S labels) x₀ r)) :
    StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper where
  fields := modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ
  design := normalizedDesign Q S θ (extendLabels S labels) x₀ r
  legal := ⟨hlegal, hd⟩
  regular := by
    have hs := modelFields_smooth side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ
    exact ⟨hs.1.of_le (WithTop.coe_le_coe.mpr le_top), hs.2.1.of_le (WithTop.coe_le_coe.mpr le_top),
      hs.2.2.of_le (WithTop.coe_le_coe.mpr le_top)⟩
  design_nonneg x := (div_nonneg (pow_nonneg (sub_nonneg.mpr hθ1.le) _) (by positivity)).trans
    ((normalizedDesign_legal Q S θ hθ hθ1 (extendLabels S labels) x₀ r).2.2 x).1

end CausalLowerbound.PartB.ShellGeometry

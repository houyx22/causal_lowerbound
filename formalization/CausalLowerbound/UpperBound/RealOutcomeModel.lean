import CausalLowerbound.UpperBound.LocalHolderTaylor
import CausalLowerbound.UpperBound.Covariance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Constructions.Pi

/-! The upper-bound model allows arbitrary real outcomes.  The conditional
law of (A,Y) is a Markov kernel, A is binary, and only a conditional second
moment of Y is imposed.  Design regularity consists solely of measurable
density bounds.  Local Hölder regularity is specified separately below. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory BigOperators Classical

namespace CausalLowerbound.UpperBound

def treatmentValue (z : Bool × ℝ) : ℝ := if z.1 then 1 else 0

theorem treatmentValue_sq (z : Bool × ℝ) : treatmentValue z ^ 2 = treatmentValue z := by
  cases z with | mk a y => cases a <;> norm_num [treatmentValue]

theorem treatmentValue_bound (z : Bool × ℝ) : ‖treatmentValue z‖ ≤ 1 := by
  cases z with | mk a y => cases a <;> norm_num [treatmentValue]

theorem measurable_treatmentValue : Measurable treatmentValue := by
  have hm : Measurable (fun a : Bool => if a then (1 : ℝ) else 0) := measurable_of_countable _
  exact hm.comp measurable_fst

theorem treatmentValue_memLp (μ : Measure (Bool × ℝ)) [IsFiniteMeasure μ] :
    MemLp treatmentValue 2 μ :=
  MemLp.of_bound measurable_treatmentValue.aestronglyMeasurable 1
    (Filter.Eventually.of_forall treatmentValue_bound)

structure RealOutcomeModel (d : Type*) [Fintype d] (ε lower upper M₂ : ℝ) where
  design : Measure (d → ℝ)
  design_probability : IsProbabilityMeasure design
  density : (d → ℝ) → ℝ
  density_measurable : Measurable density
  design_eq : design = (volume.restrict (Icc (0 : d → ℝ) 1)).withDensity
    (fun x => ENNReal.ofReal (density x))
  density_bounds : ∀ᵐ x ∂volume.restrict (Icc (0 : d → ℝ) 1),
    lower ≤ density x ∧ density x ≤ upper
  conditional : Kernel (d → ℝ) (Bool × ℝ)
  conditional_markov : IsMarkovKernel conditional
  propensity : (d → ℝ) → ℝ
  baseline : (d → ℝ) → ℝ
  effect : (d → ℝ) → ℝ
  overlap : ∀ᵐ x ∂design, ε ≤ propensity x ∧ propensity x ≤ 1 - ε
  response_memLp : ∀ᵐ x ∂design, MemLp (fun z : Bool × ℝ => z.2) 2 (conditional x)
  treatment_mean : ∀ᵐ x ∂design, (∫ z, treatmentValue z ∂conditional x) = propensity x
  response_mean : ∀ᵐ x ∂design,
    (∫ z, z.2 ∂conditional x) = baseline x + propensity x * effect x
  treated_response_mean : ∀ᵐ x ∂design,
    (∫ z, treatmentValue z * z.2 ∂conditional x) = propensity x * (baseline x + effect x)
  response_second_moment : ∀ᵐ x ∂design, (∫ z, z.2 ^ 2 ∂conditional x) ≤ M₂

attribute [instance] RealOutcomeModel.design_probability RealOutcomeModel.conditional_markov

namespace RealOutcomeModel

variable {d : Type*} [Fintype d] {ε lower upper M₂ : ℝ}
variable (M : RealOutcomeModel d ε lower upper M₂)

def observationLaw : Measure ((d → ℝ) × (Bool × ℝ)) := M.design ⊗ₘ M.conditional

instance observationLaw_probability : IsProbabilityMeasure M.observationLaw := by
  unfold observationLaw
  infer_instance

def sampleLaw (I : Type*) [Fintype I] : Measure (I → (d → ℝ) × (Bool × ℝ)) :=
  Measure.pi (fun _ : I => M.observationLaw)

instance sampleLaw_probability (I : Type*) [Fintype I] : IsProbabilityMeasure (M.sampleLaw I) := by
  unfold sampleLaw
  infer_instance

def LocalRegularity (U : Set (d → ℝ)) (qα qβ qγ : ℕ)
    (θα θβ θγ Lπ L₀ Lτ : ℝ) : Prop :=
  ContDiffOn ℝ qα M.propensity U ∧ HolderControlOn qα θα Lπ M.propensity U ∧
  ContDiffOn ℝ qβ M.baseline U ∧ HolderControlOn qβ θβ L₀ M.baseline U ∧
  ContDiffOn ℝ qγ M.effect U ∧ HolderControlOn qγ θγ Lτ M.effect U

theorem design_lower_domination :
    ENNReal.ofReal lower • volume.restrict (Icc (0 : d → ℝ) 1) ≤ M.design := by
  rw [M.design_eq, ← withDensity_const]
  exact withDensity_mono (M.density_bounds.mono
    (fun _ hx => ENNReal.ofReal_le_ofReal hx.1))

theorem design_upper_domination :
    M.design ≤ ENNReal.ofReal upper • volume.restrict (Icc (0 : d → ℝ) 1) := by
  rw [M.design_eq, ← withDensity_const]
  exact withDensity_mono (M.density_bounds.mono
    (fun _ hx => ENNReal.ofReal_le_ofReal hx.2))

theorem observationLaw_design_marginal : M.observationLaw.fst = M.design :=
  Measure.fst_compProd M.design M.conditional

theorem conditional_residual_mean_all :
    ∀ᵐ x ∂M.design, ∀ t : ℝ,
      (∫ z, z.2 - t * treatmentValue z ∂M.conditional x) =
        M.baseline x + M.propensity x * (M.effect x - t) := by
  filter_upwards [M.response_memLp, M.treatment_mean, M.response_mean] with x hY hA hmean
  intro t
  rw [integral_sub (hY.integrable one_le_two)
    (((treatmentValue_memLp (M.conditional x)).integrable one_le_two).const_mul t),
    integral_const_mul, hA, hmean]
  ring

theorem conditional_residual_mean (t : ℝ) :
    ∀ᵐ x ∂M.design,
      (∫ z, z.2 - t * treatmentValue z ∂M.conditional x) =
        M.baseline x + M.propensity x * (M.effect x - t) :=
  M.conditional_residual_mean_all.mono (fun _ hx => hx t)

/-- The diagonal covariance in the conditional score.  No fourth moment
or bounded-response assumption is needed. -/
theorem conditional_residual_covariance_all :
    ∀ᵐ x ∂M.design, ∀ t : ℝ,
      covariance (M.conditional x) treatmentValue (fun z => z.2 - t * treatmentValue z) =
        M.propensity x * (1 - M.propensity x) * (M.effect x - t) := by
  filter_upwards [M.response_memLp, M.treatment_mean, M.treated_response_mean,
    M.conditional_residual_mean_all] with x hY hA hAY hR
  intro t
  have hAlp := treatmentValue_memLp (M.conditional x)
  have he (z : Bool × ℝ) : treatmentValue z * (z.2 - t * treatmentValue z) =
      treatmentValue z * z.2 - t * treatmentValue z := by
    calc
      _ = treatmentValue z * z.2 - t * treatmentValue z ^ 2 := by ring
      _ = _ := by rw [treatmentValue_sq]
  unfold covariance
  simp_rw [he]
  rw [integral_sub (f := fun z => treatmentValue z * z.2)
    (hAlp.integrable_mul hY) ((hAlp.integrable one_le_two).const_mul t),
    integral_const_mul, hA, hAY, hR t]
  ring

theorem conditional_residual_covariance (t : ℝ) :
    ∀ᵐ x ∂M.design,
      covariance (M.conditional x) treatmentValue (fun z => z.2 - t * treatmentValue z) =
        M.propensity x * (1 - M.propensity x) * (M.effect x - t) :=
  M.conditional_residual_covariance_all.mono (fun _ hx => hx t)

end RealOutcomeModel

end CausalLowerbound.UpperBound

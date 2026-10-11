import CausalLowerbound.UniformLowerBound.ClusterBounds
import CausalLowerbound.PartB.StatisticalModel
import CausalLowerbound.CommonMarginalTesting
import CausalLowerbound.MixtureRisk

/-! The fixed uniform-design model, its actual sampling experiments, and the
fuzzy-hypothesis reduction. Risks use nonnegative integrals, so all measurable
estimators, including those with infinite risk, are covered. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace CausalLowerbound.UniformLowerBound
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt

variable {d : Type*} [Fintype d] [DecidableEq d]

abbrev UniformModel (d : Type*) [Fintype d] (α β γ : Regularity)
    (Lπ L₀ Lτ κ : ℝ) := StatisticalModel d α β γ Lπ L₀ Lτ κ 1 1

def uniformMinimaxRisk (α β γ : Regularity) (Lπ L₀ Lτ κ : ℝ) (hκ : 0 ≤ κ)
    (x₀ : d → ℝ) (n : ℕ) : ℝ≥0∞ :=
  minimaxRisk α β γ Lπ L₀ Lτ κ 1 1 hκ x₀ n

variable {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}

omit [DecidableEq d] in
theorem uniformModel_design (M : UniformModel d α β γ Lπ L₀ Lτ κ) :
    M.design = fun _ => 1 := by
  funext x
  exact le_antisymm (M.legal.2.2.2 x).2 (M.legal.2.2.2 x).1

omit [DecidableEq d] in
theorem uniformModel_sampleMeasure (M : UniformModel d α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (n : ℕ) :
    M.sampleMeasure hκ n = conditionalExperiment (uniformDesign d n) (M.sampleConditional hκ) := by
  unfold StatisticalModel.sampleMeasure
  simp only [uniformModel_design M, ENNReal.ofReal_one, withDensity_const, one_smul]
  rfl

def UniformModel.toGeneral (M : UniformModel d α β γ Lπ L₀ Lτ κ)
    (lower upper : ℝ) (hl : lower ≤ 1) (hu : 1 ≤ upper) :
    StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper where
  fields := M.fields
  design := M.design
  legal := ⟨M.legal.1, M.legal.2.1, M.legal.2.2.1,
    fun x => ⟨hl.trans (M.legal.2.2.2 x).1, (M.legal.2.2.2 x).2.trans hu⟩⟩
  regular := M.regular
  design_nonneg := M.design_nonneg

omit [DecidableEq d] in
theorem uniformMinimaxRisk_le (α β γ : Regularity) (Lπ L₀ Lτ κ lower upper : ℝ)
    (hκ : 0 ≤ κ) (hl : lower ≤ 1) (hu : 1 ≤ upper) (x₀ : d → ℝ) (n : ℕ) :
    uniformMinimaxRisk α β γ Lπ L₀ Lτ κ hκ x₀ n ≤
      minimaxRisk α β γ Lπ L₀ Lτ κ lower upper hκ x₀ n := by
  unfold uniformMinimaxRisk minimaxRisk
  apply iInf_mono
  intro est
  apply iSup_le
  intro M
  exact le_iSup (fun N : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper =>
    N.risk hκ x₀ n est.val) (UniformModel.toGeneral M lower upper hl hu)

def finitePrior {I : Type*} [Fintype I] (π : FiniteLaw I) : DiscreteLaw I where
  weight := π.weight
  nonneg := π.nonneg
  total := by simpa only [π.total] using hasSum_fintype π.weight

@[simp] theorem finitePrior_expect {I : Type*} [Fintype I] (π : FiniteLaw I) (f : I → ℝ) :
    (finitePrior π).expect f = π.expect f := by
  simp only [DiscreteLaw.expect, finitePrior, tsum_fintype, FiniteLaw.expect]

theorem finiteConditional_mixture {I X Y : Type*} [Fintype I] [MeasurableSpace X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (π : FiniteLaw I) (μ : Measure X) (K : I → X → FiniteLaw Y)
    (hK : ∀ i y, Measurable (fun x => (K i x).weight y)) :
    conditionalExperiment μ (fun x => π.mixture (fun i => K i x)) =
      (finitePrior π).mixMeasures (fun i => conditionalExperiment μ (K i)) := by
  unfold conditionalExperiment
  rw [(finitePrior π).mixMeasures_withDensity (μ.prod Measure.count)
    (fun i z => (K i z.1).weight z.2) 1
    (fun i => measurable_from_prod_countable (hK i))
    (fun i z => (K i z.1).nonneg z.2)
    (fun i z => (K i z.1).weight_le_one z.2)]
  simp only [finitePrior_expect]
  rfl

variable {I : Type*} [Fintype I]

def uniformMixtureConditional (π : FiniteLaw I)
    (family : I → UniformModel d α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    {n : ℕ} (x : Fin n → d → ℝ) : FiniteLaw (Fin n → Bool × Bool) :=
  π.mixture (fun i => (family i).sampleConditional hκ x)

theorem uniformMixtureConditional_measurable (π : FiniteLaw I)
    (family : I → UniformModel d α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (n : ℕ) (w : Fin n → Bool × Bool) :
    Measurable (fun x => (uniformMixtureConditional π family hκ x).weight w) := by
  unfold uniformMixtureConditional FiniteLaw.mixture FiniteLaw.expect
  exact Finset.measurable_sum _ (fun i _ =>
    measurable_const.mul ((family i).sampleConditional_measurable hκ n w))

def uniformMixtureDensity (π : FiniteLaw I)
    (family : I → UniformModel d α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ) (n : ℕ) :
    DensityLaw ((uniformDesign d n).prod (Measure.count : Measure (Fin n → Bool × Bool))) :=
  conditionalDensityLaw (uniformDesign d n) (uniformMixtureConditional π family hκ)
    (uniformMixtureConditional_measurable π family hκ n)

theorem uniformMixtureDensity_eq_mixture (π : FiniteLaw I)
    (family : I → UniformModel d α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ) (n : ℕ) :
    (uniformMixtureDensity π family hκ n).toMeasure =
      (finitePrior π).mixMeasures (fun i => (family i).sampleMeasure hκ n) := by
  simp_rw [uniformModel_sampleMeasure]
  exact finiteConditional_mixture π (uniformDesign d n)
    (fun i => (family i).sampleConditional hκ)
    (fun i => (family i).sampleConditional_measurable hκ n)

theorem uniformMixture_risk_le (π : FiniteLaw I)
    (family : I → UniformModel d α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (x₀ : d → ℝ) (n : ℕ) (θ : ℝ) (htarget : ∀ i, (family i).fields.effect x₀ = θ)
    (est : ((Fin n → d → ℝ) × (Fin n → Bool × Bool)) → ℝ) :
    (uniformMixtureDensity π family hκ n).risk est θ ≤
      ⨆ M : UniformModel d α β γ Lπ L₀ Lτ κ, M.risk hκ x₀ n est := by
  unfold DensityLaw.risk
  rw [uniformMixtureDensity_eq_mixture]
  apply DiscreteLaw.lintegral_mixMeasures_le
  intro i
  have hh := le_iSup (fun M : UniformModel d α β γ Lπ L₀ Lτ κ => M.risk hκ x₀ n est) (family i)
  simpa only [StatisticalModel.risk, htarget i] using hh

theorem uniformComparison_minimax_lower (π : FiniteLaw I)
    (family : Bool → I → UniformModel d α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (x₀ : d → ℝ) (n : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (htarget : ∀ side i, (family side i).fields.effect x₀ = if side then Δ else 0)
    (htv : (uniformMixtureDensity π (family true) hκ n).totalVariation
      (uniformMixtureDensity π (family false) hκ n) ≤ 1 / 2) :
    ENNReal.ofReal (Δ / 4) ≤ uniformMinimaxRisk α β γ Lπ L₀ Lτ κ hκ x₀ n := by
  apply le_iInf
  intro est
  have hh := DensityLaw.two_point_quarter
    (uniformMixtureDensity π (family true) hκ n) (uniformMixtureDensity π (family false) hκ n)
    est.val est.property 0 Δ hΔ htv
  simp only [sub_zero] at hh
  apply hh.trans
  apply max_le
  · exact uniformMixture_risk_le π (family true) hκ x₀ n Δ
      (fun i => htarget true i) est.val
  · exact uniformMixture_risk_le π (family false) hκ x₀ n 0
      (fun i => htarget false i) est.val

end CausalLowerbound.UniformLowerBound

import CausalLowerbound.PartB.StatisticalModel
import CausalLowerbound.PartB.PhysicalPriorMixture
import CausalLowerbound.MixtureRisk

/-! Prior mixtures are supported on the actual regular statistical model
class. Le Cam's bound therefore yields a lower bound after the minimax infimum. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open MeasureTheory
open scoped BigOperators Classical ENNReal
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω] [Inhabited Ω]

theorem physicalComparison_risk_le {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (μ₀ : FiniteLaw Ω)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ lower upper : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hd : ∀ labels : S → ℕ, DesignLegal lower upper (normalizedDesign Q S θ (extendLabels S labels) x₀ r))
    (hκ : 0 ≤ κ) (n : ℕ) (est : ((Fin n → d → ℝ) × (Fin n → Bool × Bool)) → ℝ) :
    (physicalComparisonDensity side S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ hlegal hκ n).risk
      est (if side then δ else 0) ≤
      ⨆ M : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper, M.risk hκ x₀ n est := by
  unfold DensityLaw.risk
  rw [physicalComparisonDensity_eq_mixture]
  unfold physicalPriorExperiment
  apply DiscreteLaw.lintegral_mixMeasures_le
  intro z
  let M := physicalStatisticalModel side S atoms θ hθ hθ1 z.1 z.2 x₀ r h a b t δ (hlegal z.2) (hd z.1)
  have ht : M.fields.effect x₀ = if side then δ else 0 := by
    change (if side then targetField x₀ h δ x₀ else 0) = _
    rw [targetField_center]
  have he : (∫⁻ y, ENNReal.ofReal |est y - (if side then δ else 0)|
      ∂conditionalExperiment (designSampleMeasure Q S θ z.1 x₀ r n)
        (fixedPhysicalConditional side S atoms x₀ r h a b t δ z.2 (hlegal z.2) hκ)) = M.risk hκ x₀ n est := by
    unfold StatisticalModel.risk
    rw [ht]
    rfl
  rw [he]
  exact le_iSup (fun M : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper => M.risk hκ x₀ n est) M

theorem physicalComparison_minimax_lower {Q : ℕ} (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (μ₀ : FiniteLaw Ω)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t δ : ℝ) (hδ : 0 ≤ δ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ lower upper : ℝ}
    (hlegal : ∀ (side : Bool) (z : S → Ω),
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hd : ∀ labels : S → ℕ, DesignLegal lower upper (normalizedDesign Q S θ (extendLabels S labels) x₀ r))
    (hκ : 0 ≤ κ) (n : ℕ)
    (htv : (physicalComparisonDensity true S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ (hlegal true) hκ n).totalVariation
      (physicalComparisonDensity false S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ (hlegal false) hκ n) ≤ 1 / 2) :
    ENNReal.ofReal (δ / 4) ≤ minimaxRisk α β γ Lπ L₀ Lτ κ lower upper hκ x₀ n := by
  apply le_iInf
  intro est
  have he := DensityLaw.two_point_quarter
    (physicalComparisonDensity true S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ (hlegal true) hκ n)
    (physicalComparisonDensity false S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ (hlegal false) hκ n)
    est.val est.property 0 δ hδ htv
  simp only [sub_zero] at he
  apply he.trans
  apply max_le
  · exact physicalComparison_risk_le true S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ (hlegal true) hd hκ n est.val
  · exact physicalComparison_risk_le false S atoms μ₀ H kernel θ hθ hθ1 x₀ r h a b t δ (hlegal false) hd hκ n est.val

end CausalLowerbound.PartB.ShellGeometry

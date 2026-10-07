import CausalLowerbound.PartC.GlobalPriors
import CausalLowerbound.PartB.StatisticalModel
import CausalLowerbound.MixtureRisk

/-! Full observation mixtures of legal statistical models. Their covariate
marginal is the common tilted design law, and their risk is bounded by the
supremum over the original statistical model class. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Classical

namespace CausalLowerbound

theorem DiscreteLaw.map_mixMeasures {I X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (π : DiscreteLaw I) (M : I → Measure X) (f : X → Y) (hf : Measurable f) :
    (π.mixMeasures M).map f = π.mixMeasures (fun i => (M i).map f) := by
  ext s hs
  simp only [Measure.map_apply hf hs, DiscreteLaw.mixMeasures,
    Measure.sum_apply _ (hf hs), Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]

namespace PartC
open PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d K J Ω : Type*} [Fintype d] [DecidableEq d]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype Ω]
  {θ : ℝ} {α β γ : Regularity} {Lπ L₀ Lτ κ lower upper : ℝ}

theorem sampleMeasure_eq_carrier
    (F : CarrierProfile d θ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (M : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hdesign : M.design = F.normalized S x₀ r) (hκ : 0 ≤ κ) (n : ℕ) :
    M.sampleMeasure hκ n = conditionalExperiment (F.sampleMeasure S x₀ r n) (M.sampleConditional hκ) := by
  unfold StatisticalModel.sampleMeasure
  rw [hdesign]
  rfl

def carrierModelMixture
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (M : (((K → ℕ) × (J → Bool)) × (K → Ω)) → StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hκ : 0 ≤ κ) : Measure ((Fin n → d → ℝ) × (Fin n → Bool × Bool)) :=
  (tiltedCarrierPrior F hθ hθ1 S x₀ r H kernel n).mixMeasures (fun z => (M z).sampleMeasure hκ n)

theorem carrierModelMixture_probability
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (M : (((K → ℕ) × (J → Bool)) × (K → Ω)) → StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hκ : 0 ≤ κ) : IsProbabilityMeasure (carrierModelMixture F hθ hθ1 S x₀ r H kernel n M hκ) := by
  letI (z : ((K → ℕ) × (J → Bool)) × (K → Ω)) := (M z).sampleMeasure_probability hκ n
  exact DiscreteLaw.mixMeasures_probability _ _

theorem carrierModelMixture_covariate
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (M : (((K → ℕ) × (J → Bool)) × (K → Ω)) → StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hdesign : ∀ z, (M z).design = (F z.1).normalized S x₀ r) (hκ : 0 ≤ κ) :
    (carrierModelMixture F hθ hθ1 S x₀ r H kernel n M hκ).map Prod.fst =
      mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n := by
  rw [carrierModelMixture, DiscreteLaw.map_mixMeasures _ _ _ measurable_fst]
  unfold mixedCarrierDesign
  congr 1
  funext z
  rw [sampleMeasure_eq_carrier (F z.1) S x₀ r (M z) (hdesign z) hκ n]
  letI := (F z.1).sampleMeasure_probability hθ hθ1 S x₀ r n
  exact conditionalExperiment_covariate _ _ ((M z).sampleConditional_measurable hκ n)

theorem carrierModelMixture_common_Xn
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (P Q : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (M₁ M₀ : (((K → ℕ) × (J → Bool)) × (K → Ω)) → StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hdesign₁ : ∀ z, (M₁ z).design = (F z.1).normalized S x₀ r)
    (hdesign₀ : ∀ z, (M₀ z).design = (F z.1).normalized S x₀ r) (hκ : 0 ≤ κ) :
    (carrierModelMixture F hθ hθ1 S x₀ r H P n M₁ hκ).map Prod.fst =
      (carrierModelMixture F hθ hθ1 S x₀ r H Q n M₀ hκ).map Prod.fst := by
  rw [carrierModelMixture_covariate F hθ hθ1 S x₀ r H P n M₁ hdesign₁ hκ,
    carrierModelMixture_covariate F hθ hθ1 S x₀ r H Q n M₀ hdesign₀ hκ,
    tiltedCarrierPrior_common_Xn F hθ hθ1 S x₀ r H P Q n]

theorem carrierModelMixture_risk_le
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (M : (((K → ℕ) × (J → Bool)) × (K → Ω)) → StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hκ : 0 ≤ κ) (δ : ℝ) (hcenter : ∀ z, (M z).fields.effect x₀ = δ)
    (est : ((Fin n → d → ℝ) × (Fin n → Bool × Bool)) → ℝ) :
    (∫⁻ y, ENNReal.ofReal |est y - δ| ∂carrierModelMixture F hθ hθ1 S x₀ r H kernel n M hκ) ≤
      ⨆ M' : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper, M'.risk hκ x₀ n est := by
  apply DiscreteLaw.lintegral_mixMeasures_le
  intro z
  have he : (∫⁻ y, ENNReal.ofReal |est y - δ| ∂(M z).sampleMeasure hκ n) =
      (M z).risk hκ x₀ n est := by
    unfold StatisticalModel.risk
    rw [hcenter z]
  rw [he]
  exact le_iSup (fun M' : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper => M'.risk hκ x₀ n est) (M z)

end PartC
end CausalLowerbound

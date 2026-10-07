import CausalLowerbound.PartC.GlobalExperiments
import CausalLowerbound.PartC.CarrierPosterior

/-! Dominated comparison laws for the actual global model mixtures.
The base measure is common to both coefficient kernels. This module
reduces the minimax bound to a TV estimate for these actual mixtures. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d K J Ω : Type*} [Fintype d] [DecidableEq d]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype Ω]
  {θ : ℝ} {α β γ : Regularity} {Lπ L₀ Lτ κ lower upper : ℝ}

def carrierModelConditional
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (M : (((K → ℕ) × (J → Bool)) × (K → Ω)) → StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hκ : 0 ≤ κ) : (Fin n → d → ℝ) → FiniteLaw (Fin n → Bool × Bool) :=
  carrierPosteriorConditional (tiltedCarrierPrior F hθ hθ1 S x₀ r H kernel n)
    (fun z => F z.1) hθ hθ1 S x₀ r (fun z => (M z).sampleConditional hκ)

theorem carrierModelConditional_measurable
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (M : (((K → ℕ) × (J → Bool)) × (K → Ω)) → StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hκ : 0 ≤ κ) (y : Fin n → Bool × Bool) :
    Measurable (fun x => (carrierModelConditional F hθ hθ1 S x₀ r H kernel n M hκ x).weight y) :=
  carrierPosteriorConditional_measurable _ _ hθ hθ1 S x₀ r _
    (fun z => (M z).sampleConditional_measurable hκ n) y

theorem carrierModelConditional_raw_weight
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (M : (((K → ℕ) × (J → Bool)) × (K → Ω)) → StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hκ : 0 ≤ κ) (x : Fin n → d → ℝ) (y : Fin n → Bool × Bool) :
    (carrierModelConditional F hθ hθ1 S x₀ r H kernel n M hκ x).weight y =
      (signBlockPrior H kernel).expect (fun z =>
        (∏ i, (F z.1).product S x₀ r (x i)) * ((M z).sampleConditional hκ x).weight y) /
      (sharedSignPrior H).expect (fun z => ∏ i, (F z).product S x₀ r (x i)) := by
  have hc := tiltedCarrierPrior_cancellation F hθ hθ1 S x₀ r H kernel n x
    (fun z => ((M z).sampleConditional hκ x).weight y)
  have hd := tiltedCarrierPrior_cancellation F hθ hθ1 S x₀ r H kernel n x (fun _ => 1)
  simp only [mul_one] at hd
  have hb (z : (K → ℕ) × (J → Bool)) :
      |∏ i, (F z).product S x₀ r (x i)| ≤ ((1 + θ) ^ (5 ^ Fintype.card d)) ^ n := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i : Fin n, (1 + θ) ^ (5 ^ Fintype.card d) := by
        apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        intro i _
        have hp := (F z).product_bounds hθ hθ1 S x₀ r (x i)
        rw [abs_of_nonneg ((pow_nonneg (sub_nonneg.mpr hθ1.le) _).trans hp.1)]
        exact hp.2
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have he := DiscreteLaw.joint_expect_label (sharedSignPrior H) (signBlockKernel kernel)
    (fun z => ∏ i, (F z).product S x₀ r (x i)) _ hb
  change (signBlockPrior H kernel).expect (fun z => ∏ i, (F z.1).product S x₀ r (x i)) = _ at he
  rw [he] at hd
  have hlo : 0 < ((1 - θ) ^ (5 ^ Fintype.card d)) ^ n :=
    pow_pos (pow_pos (sub_pos.mpr hθ1) _) _
  have hz : 0 < (sharedSignPrior H).expect (fun z => (F z).normalizer S x₀ r ^ n) :=
    hlo.trans_le ((sharedSignPrior H).expect_bounds _ _ _ hlo.le
      (carrierNormalizerPow_bounds F hθ hθ1 S x₀ r n)).1
  rw [carrierModelConditional, carrierPosteriorConditional_weight]
  change _ / _ = _
  change (tiltedCarrierPrior F hθ hθ1 S x₀ r H kernel n).expect
      (fun z => (F z.1).sampleDensity S x₀ r x * ((M z).sampleConditional hκ x).weight y) = _ at hc
  change (tiltedCarrierPrior F hθ hθ1 S x₀ r H kernel n).expect
      (fun z => (F z.1).sampleDensity S x₀ r x) = _ at hd
  rw [hc, hd]
  exact mul_div_mul_left _ _ (inv_ne_zero hz.ne')

def carrierComparisonDensity
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (base : FiniteLaw Ω)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (M : (((K → ℕ) × (J → Bool)) × (K → Ω)) → StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hκ : 0 ≤ κ) :
    DensityLaw ((mixedCarrierDesign F hθ hθ1 S x₀ r H (fun _ _ _ => base) n).prod
      (Measure.count : Measure (Fin n → Bool × Bool))) := by
  letI := mixedCarrierDesign_probability F hθ hθ1 S x₀ r H (fun _ _ _ => base) n
  exact conditionalDensityLaw _ (carrierModelConditional F hθ hθ1 S x₀ r H kernel n M hκ)
    (carrierModelConditional_measurable F hθ hθ1 S x₀ r H kernel n M hκ)

theorem carrierComparisonDensity_eq_mixture
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (base : FiniteLaw Ω)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (M : (((K → ℕ) × (J → Bool)) × (K → Ω)) → StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hdesign : ∀ z, (M z).design = (F z.1).normalized S x₀ r) (hκ : 0 ≤ κ) :
    (carrierComparisonDensity F hθ hθ1 S x₀ r H base kernel n M hκ).toMeasure =
      carrierModelMixture F hθ hθ1 S x₀ r H kernel n M hκ := by
  change conditionalExperiment (mixedCarrierDesign F hθ hθ1 S x₀ r H (fun _ _ _ => base) n)
    (carrierModelConditional F hθ hθ1 S x₀ r H kernel n M hκ) = _
  rw [tiltedCarrierPrior_common_Xn F hθ hθ1 S x₀ r H (fun _ _ _ => base) kernel n]
  unfold mixedCarrierDesign carrierModelConditional
  rw [carrierPosteriorConditional_eq_mixture _ _ hθ hθ1 S x₀ r _
    (fun z => (M z).sampleConditional_measurable hκ n)]
  unfold carrierModelMixture
  congr 1
  funext z
  exact (sampleMeasure_eq_carrier (F z.1) S x₀ r (M z) (hdesign z) hκ n).symm

theorem carrierComparison_risk_le
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (base : FiniteLaw Ω)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (M : (((K → ℕ) × (J → Bool)) × (K → Ω)) → StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hdesign : ∀ z, (M z).design = (F z.1).normalized S x₀ r) (hκ : 0 ≤ κ)
    (δ : ℝ) (hcenter : ∀ z, (M z).fields.effect x₀ = δ)
    (est : ((Fin n → d → ℝ) × (Fin n → Bool × Bool)) → ℝ) :
    (carrierComparisonDensity F hθ hθ1 S x₀ r H base kernel n M hκ).risk est δ ≤
      ⨆ M' : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper, M'.risk hκ x₀ n est := by
  unfold DensityLaw.risk
  rw [carrierComparisonDensity_eq_mixture F hθ hθ1 S x₀ r H base kernel n M hdesign hκ]
  exact carrierModelMixture_risk_le F hθ hθ1 S x₀ r H kernel n M hκ δ hcenter est

/-- Conditional reduction only: the TV hypothesis still has to be proved
for the concrete mixed-case carrier sequence. -/
theorem carrierComparison_minimax_lower
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (base : FiniteLaw Ω)
    (P Q : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (M₁ M₀ : (((K → ℕ) × (J → Bool)) × (K → Ω)) → StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hdesign₁ : ∀ z, (M₁ z).design = (F z.1).normalized S x₀ r)
    (hdesign₀ : ∀ z, (M₀ z).design = (F z.1).normalized S x₀ r)
    (hκ : 0 ≤ κ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hcenter₁ : ∀ z, (M₁ z).fields.effect x₀ = δ) (hcenter₀ : ∀ z, (M₀ z).fields.effect x₀ = 0)
    (htv : (carrierComparisonDensity F hθ hθ1 S x₀ r H base P n M₁ hκ).totalVariation
      (carrierComparisonDensity F hθ hθ1 S x₀ r H base Q n M₀ hκ) ≤ 1 / 2) :
    ENNReal.ofReal (δ / 4) ≤ minimaxRisk α β γ Lπ L₀ Lτ κ lower upper hκ x₀ n := by
  apply le_iInf
  intro est
  have he := DensityLaw.two_point_quarter
    (carrierComparisonDensity F hθ hθ1 S x₀ r H base P n M₁ hκ)
    (carrierComparisonDensity F hθ hθ1 S x₀ r H base Q n M₀ hκ) est.val est.property 0 δ hδ htv
  simp only [sub_zero] at he
  apply he.trans
  exact max_le (carrierComparison_risk_le F hθ hθ1 S x₀ r H base P n M₁ hdesign₁ hκ δ hcenter₁ est.val)
    (carrierComparison_risk_le F hθ hθ1 S x₀ r H base Q n M₀ hdesign₀ hκ 0 hcenter₀ est.val)

end CausalLowerbound.PartC

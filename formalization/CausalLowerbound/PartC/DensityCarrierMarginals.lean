import CausalLowerbound.DiscreteIntegration
import CausalLowerbound.FiniteMixture
import Mathlib.MeasureTheory.Integral.Pi

/-! Marginals of a fixed countable density carrier. The density family
and label law stay fixed while the number of observation coordinates
changes. Bounded coefficient weights are projected together with the
actual density product. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
variable {X I K G Ω : Type*} [Fintype I] [Fintype K] [Fintype G] [Fintype Ω]

def carrierTensor (density : ℕ → X → ℝ) (label : ℕ) (u : I → X) : ℝ :=
  ∏ i, density label (u i)

def carrierMarginal (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ) (u : I → X) : ℝ :=
  H.expect (fun label => carrierTensor density label u)

def weightedCarrierMarginal (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ)
    (g : ℕ → ℝ) (u : I → X) : ℝ :=
  H.expect (fun label => carrierTensor density label u * g label)

theorem carrierTensor_equiv (density : ℕ → X → ℝ) (label : ℕ) (e : I ≃ K) (u : K → X) :
    carrierTensor density label (u ∘ e) = carrierTensor density label u :=
  Equiv.prod_comp e (fun i => density label (u i))

theorem carrierTensor_sum (density : ℕ → X → ℝ) (label : ℕ) (u : K → X) (z : G → X) :
    carrierTensor density label (Sum.elim u z) = carrierTensor density label u * carrierTensor density label z := by
  simp only [carrierTensor, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem carrierTensor_abs_le (density : ℕ → X → ℝ) (B : ℝ)
    (hb : ∀ label x, |density label x| ≤ B) (label : ℕ) (u : I → X) :
    |carrierTensor density label u| ≤ B ^ Fintype.card I := by
  simp only [carrierTensor, Finset.abs_prod]
  simpa using Finset.prod_le_prod (s := Finset.univ)
    (fun i _ => abs_nonneg (density label (u i))) (fun i _ => hb label (u i))

theorem carrierTensor_bounds (density : ℕ → X → ℝ) (lower upper : ℝ) (hlo : 0 ≤ lower)
    (hb : ∀ label x, lower ≤ density label x ∧ density label x ≤ upper) (label : ℕ) (u : I → X) :
    lower ^ Fintype.card I ≤ carrierTensor density label u ∧
      carrierTensor density label u ≤ upper ^ Fintype.card I := by
  constructor
  · simpa only [carrierTensor, Finset.prod_const, Finset.card_univ] using
      Finset.prod_le_prod (s := Finset.univ) (fun _ _ => hlo) (fun i _ => (hb label (u i)).1)
  · simpa only [carrierTensor, Finset.prod_const, Finset.card_univ] using
      Finset.prod_le_prod (s := Finset.univ) (fun i _ => hlo.trans (hb label (u i)).1)
        (fun i _ => (hb label (u i)).2)

theorem carrierMarginal_bounds (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ)
    (lower upper : ℝ) (hlo : 0 ≤ lower)
    (hb : ∀ label x, lower ≤ density label x ∧ density label x ≤ upper) (u : I → X) :
    lower ^ Fintype.card I ≤ carrierMarginal H density u ∧
      carrierMarginal H density u ≤ upper ^ Fintype.card I :=
  H.expect_bounds _ _ _ (pow_nonneg hlo _) (fun label => carrierTensor_bounds density lower upper hlo hb label u)

theorem weightedCarrierMarginal_eq_of_hasSum (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ)
    (g : ℕ → ℝ) (u : I → X) (v : ℝ)
    (hs : HasSum (fun label => (H.weight label * g label) * carrierTensor density label u) v) :
    weightedCarrierMarginal H density g u = v := by
  rw [← hs.tsum_eq]
  apply tsum_congr
  intro label
  ring

theorem carrierTensor_continuous [TopologicalSpace X] (density : ℕ → X → ℝ)
    (hc : ∀ label, Continuous (density label)) (label : ℕ) :
    Continuous (carrierTensor (I := I) density label) :=
  continuous_finset_prod _ (fun i _ => (hc label).comp (continuous_apply i))

theorem weightedCarrierMarginal_continuous [TopologicalSpace X]
    (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ) (g : ℕ → ℝ) (B M : ℝ) (hB : 0 ≤ B)
    (hc : ∀ label, Continuous (density label)) (hb : ∀ label x, |density label x| ≤ B)
    (hg : ∀ label, |g label| ≤ M) : Continuous (weightedCarrierMarginal (I := I) H density g) := by
  apply H.expect_continuous _ (B ^ Fintype.card I * M)
    (fun label => (carrierTensor_continuous density hc label).mul continuous_const)
  intro label u
  rw [abs_mul]
  exact mul_le_mul (carrierTensor_abs_le density B hb label u) (hg label) (abs_nonneg _) (pow_nonneg hB _)

theorem carrierTensor_integral [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (density : ℕ → X → ℝ) (hint : ∀ label, (∫ x, density label x ∂μ) = 1) (label : ℕ) :
    (∫ u : I → X, carrierTensor density label u ∂Measure.pi (fun _ : I => μ)) = 1 := by
  have he := @integral_fintype_prod_eq_prod ℝ inferInstance I inferInstance (fun _ => X)
    (fun _ => density label) (fun _ => ⟨μ⟩) (fun _ => inferInstanceAs (SigmaFinite μ))
  change (∫ u : I → X, carrierTensor density label u ∂Measure.pi (fun _ : I => μ)) =
    ∏ _ : I, ∫ x, density label x ∂μ at he
  simpa only [hint label, Finset.prod_const_one] using he

theorem weightedCarrierMarginal_projective [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ) (g : ℕ → ℝ) (B M : ℝ) (hB : 0 ≤ B)
    (hc : ∀ label, Continuous (density label)) (hb : ∀ label x, |density label x| ≤ B)
    (hint : ∀ label, (∫ x, density label x ∂μ) = 1) (hg : ∀ label, |g label| ≤ M) (u : K → X) :
    (∫ z : G → X, weightedCarrierMarginal H density g (Sum.elim u z)
      ∂Measure.pi (fun _ : G => μ)) = weightedCarrierMarginal H density g u := by
  have hcont (label : ℕ) : Continuous (fun z : G → X => carrierTensor density label (Sum.elim u z) * g label) := by
    simp_rw [carrierTensor_sum]
    exact (continuous_const.mul (carrierTensor_continuous density hc label)).mul continuous_const
  unfold weightedCarrierMarginal
  rw [H.integral_expect (Measure.pi (fun _ : G => μ)) _ (B ^ Fintype.card (K ⊕ G) * M)
    (fun label => (hcont label).aestronglyMeasurable) (fun label z => ?_)]
  · simp only [carrierTensor_sum, integral_mul_const, integral_const_mul, carrierTensor_integral μ density hint, mul_one]
  · rw [abs_mul]
    exact mul_le_mul (carrierTensor_abs_le density B hb label (Sum.elim u z)) (hg label)
      (abs_nonneg _) (pow_nonneg hB _)

theorem weightedCarrierMarginal_completed [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ) (g : ℕ → ℝ) (B M : ℝ) (hB : 0 ≤ B)
    (hc : ∀ label, Continuous (density label)) (hb : ∀ label x, |density label x| ≤ B)
    (hint : ∀ label, (∫ x, density label x ∂μ) = 1) (hg : ∀ label, |g label| ≤ M)
    (e : K ⊕ G ≃ I) (u : K → X) :
    (∫ z : G → X, weightedCarrierMarginal H density g (Sum.elim u z ∘ e.symm)
      ∂Measure.pi (fun _ : G => μ)) = weightedCarrierMarginal H density g u := by
  have he (z : G → X) : weightedCarrierMarginal H density g (Sum.elim u z ∘ e.symm) =
      weightedCarrierMarginal H density g (Sum.elim u z) := by
    simp only [weightedCarrierMarginal, carrierTensor_equiv]
  simp_rw [he]
  exact weightedCarrierMarginal_projective μ H density g B M hB hc hb hint hg u

theorem coefficient_difference_bound (kernel : ℕ → FiniteLaw Ω) (μ : FiniteLaw Ω)
    (f : Ω → ℝ) (label : ℕ) :
    |(kernel label).expect f - μ.expect f| ≤ 2 * ∑ y, |f y| := by
  have hb (y : Ω) : |f y| ≤ ∑ z, |f z| :=
    Finset.single_le_sum (fun z _ => abs_nonneg (f z)) (Finset.mem_univ y)
  exact (abs_sub _ _).trans ((add_le_add ((kernel label).abs_expect_le_bound f _ hb)
    (μ.abs_expect_le_bound f _ hb)).trans_eq (by ring))

end CausalLowerbound.PartC

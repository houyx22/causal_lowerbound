import CausalLowerbound.PartC.CarrierDesign
import CausalLowerbound.PartC.SharedSignPriors

/-! The actual design-normalizer tilt of a shared-sign prior. The two
coefficient kernels induce exactly the same covariate experiment. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.PartC
variable {d K J Ω : Type*} [Fintype d] [DecidableEq d]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype Ω] {θ : ℝ}

theorem carrierNormalizerPow_bounds
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) (z : (K → ℕ) × (J → Bool)) :
    ((1 - θ) ^ (5 ^ Fintype.card d)) ^ n ≤ (F z).normalizer S x₀ r ^ n ∧
      (F z).normalizer S x₀ r ^ n ≤ ((1 + θ) ^ (5 ^ Fintype.card d)) ^ n := by
  have hb := (F z).normalizer_bounds hθ hθ1 S x₀ r
  have hl := pow_nonneg (sub_nonneg.mpr hθ1.le) (5 ^ Fintype.card d)
  exact ⟨pow_le_pow_left₀ hl hb.1 n, pow_le_pow_left₀ (hl.trans hb.1) hb.2 n⟩

def tiltedCarrierPrior
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) :
    DiscreteLaw (((K → ℕ) × (J → Bool)) × (K → Ω)) :=
  (signBlockPrior H kernel).tilt (fun z => (F z.1).normalizer S x₀ r ^ n)
    (((1 - θ) ^ (5 ^ Fintype.card d)) ^ n) (((1 + θ) ^ (5 ^ Fintype.card d)) ^ n)
    (pow_pos (pow_pos (sub_pos.mpr hθ1) _) _)
    (fun z => carrierNormalizerPow_bounds F hθ hθ1 S x₀ r n z.1)

theorem tiltedCarrierPrior_common_environment [MeasurableSpace Ω]
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (P Q : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) :
    (tiltedCarrierPrior F hθ hθ1 S x₀ r H P n).toMeasure.map Prod.fst =
      (tiltedCarrierPrior F hθ hθ1 S x₀ r H Q n).toMeasure.map Prod.fst :=
  signBlockPrior_tilt_common_environment H P Q _ _ _ _
    (carrierNormalizerPow_bounds F hθ hθ1 S x₀ r n)

theorem tiltedCarrierPrior_cancellation
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (x : Fin n → d → ℝ) (L : (((K → ℕ) × (J → Bool)) × (K → Ω)) → ℝ) :
    (tiltedCarrierPrior F hθ hθ1 S x₀ r H kernel n).expect
      (fun z => (∏ i, (F z.1).normalized S x₀ r (x i)) * L z) =
      ((sharedSignPrior H).expect (fun z => (F z).normalizer S x₀ r ^ n))⁻¹ *
        (signBlockPrior H kernel).expect (fun z => (∏ i, (F z.1).product S x₀ r (x i)) * L z) := by
  have hc := DiscreteLaw.tilt_likelihood_cancellation (signBlockPrior H kernel)
    (fun z => (F z.1).normalizer S x₀ r) n
    ((1 - θ) ^ (5 ^ Fintype.card d)) ((1 + θ) ^ (5 ^ Fintype.card d))
    (pow_pos (sub_pos.mpr hθ1) _) (fun z => (F z.1).normalizer_bounds hθ hθ1 S x₀ r)
    (fun z i => (F z.1).product S x₀ r (x i)) L
  have hb (z : (K → ℕ) × (J → Bool)) :
      |(F z).normalizer S x₀ r ^ n| ≤ ((1 + θ) ^ (5 ^ Fintype.card d)) ^ n := by
    have hz := carrierNormalizerPow_bounds F hθ hθ1 S x₀ r n z
    rw [abs_of_nonneg ((pow_nonneg (pow_nonneg (sub_nonneg.mpr hθ1.le) _) _).trans hz.1)]
    exact hz.2
  have he := DiscreteLaw.joint_expect_label (sharedSignPrior H) (signBlockKernel kernel)
    (fun z => (F z).normalizer S x₀ r ^ n) _ hb
  change (signBlockPrior H kernel).expect (fun z => (F z.1).normalizer S x₀ r ^ n) = _ at he
  rw [he] at hc
  exact hc

def mixedCarrierDesign
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) :
    Measure (Fin n → d → ℝ) :=
  (tiltedCarrierPrior F hθ hθ1 S x₀ r H kernel n).mixMeasures
    (fun z => (F z.1).sampleMeasure S x₀ r n)

theorem mixedCarrierDesign_probability
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) :
    IsProbabilityMeasure (mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) := by
  letI (z : ((K → ℕ) × (J → Bool)) × (K → Ω)) :=
    (F z.1).sampleMeasure_probability hθ hθ1 S x₀ r n
  exact DiscreteLaw.mixMeasures_probability _ _

theorem tiltedCarrierPrior_common_Xn
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (P Q : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) :
    mixedCarrierDesign F hθ hθ1 S x₀ r H P n =
      mixedCarrierDesign F hθ hθ1 S x₀ r H Q n :=
  DiscreteLaw.tilted_common_mixture (sharedSignPrior H) (signBlockKernel P) (signBlockKernel Q)
    (fun z => (F z).normalizer S x₀ r ^ n)
    (((1 - θ) ^ (5 ^ Fintype.card d)) ^ n) (((1 + θ) ^ (5 ^ Fintype.card d)) ^ n)
    (pow_pos (pow_pos (sub_pos.mpr hθ1) _) _) (carrierNormalizerPow_bounds F hθ hθ1 S x₀ r n)
    (fun z => (F z).sampleMeasure S x₀ r n)

end CausalLowerbound.PartC

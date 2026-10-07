import CausalLowerbound.PartC.DensityCarrierMarginals
import CausalLowerbound.DiscreteMixture
import CausalLowerbound.FiniteProductMixture

/-! Genuine finite coefficient laws after observing a density-carrier
sample. The posterior uses the full countable label law and its positive
design normalizer. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
variable {X I K Ω : Type*} [Fintype I] [Fintype K] [Fintype Ω]

def densityCarrierPosterior (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ)
    (kernel : ℕ → FiniteLaw Ω) (lower upper : ℝ) (hlo : 0 < lower)
    (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper) (u : I → X) : FiniteLaw Ω :=
  (H.tilt (fun n => carrierTensor density n u) (lower ^ Fintype.card I) (upper ^ Fintype.card I)
    (pow_pos hlo _) (fun n => carrierTensor_bounds density lower upper hlo.le hb n u)).mixFinite kernel

theorem carrierMarginal_pos (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ)
    (lower upper : ℝ) (hlo : 0 < lower)
    (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper) (u : I → X) :
    0 < carrierMarginal H density u :=
  (pow_pos hlo _).trans_le (carrierMarginal_bounds H density lower upper hlo.le hb u).1

theorem densityCarrierPosterior_expect (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ)
    (kernel : ℕ → FiniteLaw Ω) (lower upper : ℝ) (hlo : 0 < lower)
    (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper) (u : I → X) (f : Ω → ℝ) :
    (densityCarrierPosterior H density kernel lower upper hlo hb u).expect f =
      (carrierMarginal H density u)⁻¹ * weightedCarrierMarginal H density (fun n => (kernel n).expect f) u := by
  rw [densityCarrierPosterior, DiscreteLaw.mixFinite_expect, DiscreteLaw.tilt_expect]
  rfl

theorem densityCarrierPosterior_constant (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ)
    (μ : FiniteLaw Ω) (lower upper : ℝ) (hlo : 0 < lower)
    (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper) (u : I → X) :
    densityCarrierPosterior H density (fun _ => μ) lower upper hlo hb u = μ := by
  apply FiniteLaw.ext
  intro y
  change (H.tilt _ _ _ _ _).expect (fun _ => μ.weight y) = μ.weight y
  rw [DiscreteLaw.expect, tsum_mul_right, DiscreteLaw.tsum_weight, one_mul]

theorem densityCarrierPosterior_difference (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ)
    (P Q : ℕ → FiniteLaw Ω) (lower upper : ℝ) (hlo : 0 < lower)
    (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper) (u : I → X) (f : Ω → ℝ) :
    (densityCarrierPosterior H density Q lower upper hlo hb u).expect f -
      (densityCarrierPosterior H density P lower upper hlo hb u).expect f =
        (carrierMarginal H density u)⁻¹ * weightedCarrierMarginal H density
          (fun n => (Q n).expect f - (P n).expect f) u :=
  H.posterior_moment_difference P Q _ _ _ _ _ f

theorem densityCarrierPosterior_increment (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ)
    (kernel : ℕ → FiniteLaw Ω) (μ : FiniteLaw Ω) (lower upper : ℝ) (hlo : 0 < lower)
    (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper) (u : I → X) (f : Ω → ℝ) :
    (densityCarrierPosterior H density kernel lower upper hlo hb u).expect f - μ.expect f =
      (carrierMarginal H density u)⁻¹ * weightedCarrierMarginal H density
        (fun n => (kernel n).expect f - μ.expect f) u := by
  simpa only [densityCarrierPosterior_constant] using
    densityCarrierPosterior_difference H density (fun _ => μ) kernel lower upper hlo hb u f

theorem densityCarrierPosterior_equiv (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ)
    (kernel : ℕ → FiniteLaw Ω) (lower upper : ℝ) (hlo : 0 < lower)
    (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper) (e : I ≃ K) (u : K → X) :
    densityCarrierPosterior H density kernel lower upper hlo hb (u ∘ e) =
      densityCarrierPosterior H density kernel lower upper hlo hb u := by
  unfold densityCarrierPosterior
  congr 1
  apply DiscreteLaw.ext
  intro n
  simp only [DiscreteLaw.tilt, carrierTensor_equiv]

end CausalLowerbound.PartC

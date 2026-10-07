import CausalLowerbound.PartC.RetainedDesignProduct
import CausalLowerbound.PartC.SharedPolynomialMoments

/-! The raw sample-design expectation is exactly a sum of products of
retained weighted moments, with the shared signs kept outside. No
normalizer or design factor is dropped in passing to the polynomial. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry MvPolynomial
variable {d I J A Ω : Type*} [Fintype d] [DecidableEq d] [Fintype I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A] [Fintype Ω]

theorem raw_design_weighted_polynomial_moments (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ)
    (F : ((S → ℕ) × (J → Bool)) → CarrierProfile d θ)
    (density : S → (J → Bool) → ℕ → (d → ℝ) → ℝ)
    (hF : ∀ labels ζ (k : S) u, (F (labels, ζ)).density k.val u = density k ζ (labels k) u)
    (H : S → DiscreteLaw ℕ) (kernel : S → (J → Bool) → ℕ → FiniteLaw Ω)
    (atoms : Ω → A → ℝ) (x₀ : d → ℝ) (r : ℝ) (x : I → d → ℝ)
    (p : (J → Bool) → MvPolynomial (S × A) ℝ) :
    (signBlockPrior H kernel).expect (fun v =>
      (∏ i, (F v.1).product S x₀ r (x i)) * eval (fun ka => atoms (v.2 ka.1) ka.2) (p v.1.2)) =
      independentSigns.expect (fun ζ => ∑ m ∈ (p ζ).support, (p ζ).coeff m * ∏ k : S,
        weightedCarrierMarginal (H k) (density k ζ)
          (fun n => (kernel k ζ n).expect (fun u => eval (atoms u) (blockMonomial m k)))
          (fun i : {i // x i ∈ carrierBox x₀ r k.val} =>
            carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) := by
  have hd (k : S) (ζ : J → Bool) (n : ℕ) (u : d → ℝ) : |density k ζ n u| ≤ 1 + θ := by
    have hh := (F ((fun _ => n), ζ)).bounds k.val u
    rw [hF (fun _ => n) ζ k u] at hh
    exact abs_le.mpr ⟨by linarith [hh.1], hh.2⟩
  have he (labels : S → ℕ) (ζ : J → Bool) :
      (∏ i, (F (labels, ζ)).product S x₀ r (x i)) =
        ∏ k : S, carrierTensor (density k ζ) (labels k)
          (fun i : {i // x i ∈ carrierBox x₀ r k.val} =>
            carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) := by
    rw [CarrierProfile.sample_product_retained]
    simp only [carrierTensor, hF]
  have ht (k : S) (ζ : J → Bool) (n : ℕ) :
      |carrierTensor (density k ζ) n
        (fun i : {i // x i ∈ carrierBox x₀ r k.val} =>
          carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))| ≤
        (1 + θ) ^ Fintype.card {i // x i ∈ carrierBox x₀ r k.val} :=
    carrierTensor_abs_le _ (1 + θ) (hd k ζ) n _
  have hev (v : ((S → ℕ) × (J → Bool)) × (S → Ω)) := he v.1.1 v.1.2
  simp_rw [hev]
  exact signBlockPrior_weighted_polynomial_expect H kernel atoms _
    (fun k => (1 + θ) ^ Fintype.card {i // x i ∈ carrierBox x₀ r k.val})
    (fun _ => pow_nonneg (by linarith) _) ht p

end CausalLowerbound.PartC

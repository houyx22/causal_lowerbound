import CausalLowerbound.PartC.LocalPropensityProjectivity
import CausalLowerbound.PartC.SharedPolynomialMoments

/-! Assemble the one-block retained/ghost identities into a full
design-weighted polynomial identity. A single common sign configuration
is used in every factor and averaged only after taking their product. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d K : Type*} [Fintype d] [DecidableEq d] [Fintype K] [DecidableEq K]

theorem physical_multiblock_polynomial_projection
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (block : K → d → ℤ)
    (c w N N₀ θ ja t τ C δ : ℝ) (hθ : 0 ≤ θ)
    (hcarr : ∀ k, HasPaperPropensityCarrier Q ρ x₀ ℓ r h (block k) c w N N₀ θ ja t τ C δ)
    (B : K → Representative.Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (H : K → DiscreteLaw ℕ)
    (kernel : K → (activeBlocks (d := d) ℓ h → Bool) → ℕ →
      FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (A G : K → Type) [∀ k, Fintype (A k)] [∀ k, Fintype (G k)]
    (e : ∀ k, A k ⊕ G k ≃ Fin Q) (u : ∀ k, A k → d → ℝ)
    (hproject : ∀ k ζ (p : MvPolynomial (CoefficientExponent d Q) ℝ), p.totalDegree ≤ 4 * Q →
      weightedCarrierMarginal (H k)
        (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h (block k) c w N θ n ζ)
        (fun n => (kernel k ζ n).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p)) (u k) =
        ∫ z : G k → d → ℝ,
          (paperCoefficientLaw Q).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p) *
            physicalCarrierValue x₀ ℓ r h (block k) c w N (B k) ζ (completedConfiguration (e k) (u k) z) +
          physicalPropensityIncrementValue Q ρ x₀ ℓ r h (block k) c w N ja t τ (B k) ζ p
            (completedConfiguration (e k) (u k) z) ∂Measure.pi (fun _ : G k => cubeMeasure d))
    (p : (activeBlocks (d := d) ℓ h → Bool) → MvPolynomial (K × CoefficientExponent d Q) ℝ)
    (hp : ∀ ζ, (p ζ).totalDegree ≤ 4 * Q) :
    (signBlockPrior H kernel).expect (fun v =>
      (∏ k, carrierTensor
        (fun n => carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h (block k) c w N θ n v.1.2)
        (v.1.1 k) (u k)) * eval (fun ka => paperCoefficientAtoms Q ρ (v.2 ka.1) ka.2) (p v.1.2)) =
      independentSigns.expect (fun ζ => ∑ m ∈ (p ζ).support, (p ζ).coeff m * ∏ k,
        ∫ z : G k → d → ℝ,
          (paperCoefficientLaw Q).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) (blockMonomial m k)) *
            physicalCarrierValue x₀ ℓ r h (block k) c w N (B k) ζ (completedConfiguration (e k) (u k) z) +
          physicalPropensityIncrementValue Q ρ x₀ ℓ r h (block k) c w N ja t τ (B k) ζ
            (blockMonomial m k) (completedConfiguration (e k) (u k) z)
              ∂Measure.pi (fun _ : G k => cubeMeasure d)) := by
  have hd (k : K) (ζ : activeBlocks (d := d) ℓ h → Bool) (n : ℕ) (v : d → ℝ) :
      |carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h (block k) c w N θ n ζ v| ≤ 1 + θ := by
    have hb := (hcarr k).2.2.1 n ζ v
    exact abs_le.mpr ⟨by linarith [hb.1], hb.2⟩
  rw [signBlockPrior_weighted_polynomial_expect H kernel (paperCoefficientAtoms Q ρ) _
    (fun k => (1 + θ) ^ Fintype.card (A k)) (fun _ => pow_nonneg (by linarith) _)
    (fun k ζ n => carrierTensor_abs_le _ (1 + θ) (hd k ζ) n (u k)) p]
  apply FiniteLaw.expect_congr
  intro ζ
  apply Finset.sum_congr rfl
  intro m hm
  apply congrArg (fun v : ℝ => (p ζ).coeff m * v)
  apply Finset.prod_congr rfl
  intro k _
  exact hproject k ζ (blockMonomial m k) ((blockMonomial_degree_le (p ζ) m hm k).trans (hp ζ))

end CausalLowerbound.PartC

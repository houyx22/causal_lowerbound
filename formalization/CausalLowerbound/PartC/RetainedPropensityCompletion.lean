import CausalLowerbound.PartC.UnitCubeGhosts
import CausalLowerbound.PartC.PropensityLikelihoodPolynomials
import CausalLowerbound.PartC.PhysicalLocalPropensityMatching

/-! Retained-site cells embedded in a full configuration. Ghost cells
are exactly one when their two observation coefficients are zero. This
allows the full shared-sign matching theorem to apply without changing
the representative, density degrees, or physical rough field. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative RoughPropensity
variable {I G V d : Type*} [Fintype I] [Fintype G] [Fintype V] [Fintype d] [DecidableEq d]

theorem retainedPropensityPolynomial_completed (Q : ℕ) (e : I ⊕ G ≃ V) (R T : I → ℝ)
    (ja rough offset ψ : V → ℝ) (sites : V → d → ℝ) :
    retainedPropensityPolynomial Q (completedSites e R (fun _ => 0)) (completedSites e T (fun _ => 0))
      ja rough offset ψ sites =
      retainedPropensityPolynomial Q R T (fun i => ja (e (Sum.inl i))) (fun i => rough (e (Sum.inl i)))
        (fun i => offset (e (Sum.inl i))) (fun i => ψ (e (Sum.inl i))) (fun i => sites (e (Sum.inl i))) := by
  unfold retainedPropensityPolynomial
  rw [← e.prod_comp (fun j => propensityCellPolynomial (completedSites e R (fun _ => 0) j)
    (completedSites e T (fun _ => 0) j) (ja j) (rough j) (retainedFieldPolynomial Q (offset j) (ψ j) (sites j)))]
  simp only [Fintype.prod_sum_type, completedSites_retained, completedSites_ghost]
  simp [propensityCellPolynomial]

theorem propensity_likelihood_prod_completed (e : I ⊕ G ≃ V) (R T : I → ℝ)
    (ja smooth rough : V → ℝ) :
    (∏ j, likelihood (completedSites e R (fun _ => 0) j) (completedSites e T (fun _ => 0) j)
      (ja j) (smooth j) (rough j)) =
      ∏ i, likelihood (R i) (T i) (ja (e (Sum.inl i))) (smooth (e (Sum.inl i))) (rough (e (Sum.inl i))) := by
  rw [← e.prod_comp (fun j => likelihood (completedSites e R (fun _ => 0) j)
    (completedSites e T (fun _ => 0) j) (ja j) (smooth j) (rough j))]
  simp only [Fintype.prod_sum_type, completedSites_retained, completedSites_ghost]
  simp [likelihood]

theorem propensity_real_prod_completed (e : I ⊕ G ≃ V) (R T : I → ℝ)
    (ja smooth rough δ : V → ℝ) :
    (∏ j, (likelihood (completedSites e R (fun _ => 0) j) (completedSites e T (fun _ => 0) j)
      (ja j) (smooth j) (rough j) +
      realField (completedSites e R (fun _ => 0) j) (completedSites e T (fun _ => 0) j)
        (ja j) (δ j) (rough j))) =
      ∏ i, (likelihood (R i) (T i) (ja (e (Sum.inl i))) (smooth (e (Sum.inl i))) (rough (e (Sum.inl i))) +
        realField (R i) (T i) (ja (e (Sum.inl i))) (δ (e (Sum.inl i))) (rough (e (Sum.inl i)))) := by
  rw [← e.prod_comp (fun j => likelihood (completedSites e R (fun _ => 0) j)
    (completedSites e T (fun _ => 0) j) (ja j) (smooth j) (rough j) +
      realField (completedSites e R (fun _ => 0) j) (completedSites e T (fun _ => 0) j)
        (ja j) (δ j) (rough j))]
  simp only [Fintype.prod_sum_type, completedSites_retained, completedSites_ghost]
  simp [likelihood, realField]

theorem removed_physical_propensity_retained_matching [LinearOrder V]
    {Ω : Type*} [Fintype Ω] (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h) (x : V → d → ℝ)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (e : I ⊕ G ≃ V) (R T : I → ℝ) (ja scale offset ψ : V → ℝ)
    (W : Representative.Array d V (activeBlocks (d := d) ℓ h) 1) (u : V × d → ℝ) (τ amp : ℝ) :
    let keep : I → V := fun i => e (Sum.inl i)
    let B := remove (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) W
    independentSigns.expect (fun ζ =>
      propensityCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ
        (fun i => scale i ^ 2 * ja i ^ 2 * (coarseBump x₀ h (x i) ^ 2) ^ 2) B u
        (fun i => scale i * physicalRoughField x₀ ℓ h ζ (x i)) ζ
        (retainedPropensityPolynomial Q R T (ja ∘ keep)
          (fun i => physicalRoughField x₀ ℓ h ζ (x (keep i))) (offset ∘ keep) (ψ ∘ keep)
          (configurationSite u ∘ keep))) =
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) *
        μ.expect (fun ξ => independentSigns.expect (fun ζ =>
          pointValue (torusProjection u) (fun i => scale i * physicalRoughField x₀ ℓ h ζ (x i)) ζ B *
            ((∏ i, (likelihood (R i) (T i) (ja (keep i))
              (offset (keep i) + ψ (keep i) * coefficientEvaluation (U ξ) (configurationSite u (keep i)))
                (physicalRoughField x₀ ℓ h ζ (x (keep i))) +
              realField (R i) (T i) (ja (keep i))
                (ja (keep i) * (ψ (keep i) * amp) * scale (keep i) * coarseBump x₀ h (x (keep i)) ^ 2)
                (physicalRoughField x₀ ℓ h ζ (x (keep i))))) -
              ∏ i, likelihood (R i) (T i) (ja (keep i))
                (offset (keep i) + ψ (keep i) * coefficientEvaluation (U ξ) (configurationSite u (keep i)))
                (physicalRoughField x₀ ℓ h ζ (x (keep i)))))) := by
  have he := removed_physical_propensity_coefficient_matching Q hQ hcard μ U x₀ ℓ h hℓ hh x hsep
    (completedSites e R (fun _ => 0)) (completedSites e T (fun _ => 0)) ja scale offset ψ W u τ amp
  simpa only [retainedPropensityPolynomial_completed, propensity_real_prod_completed,
    propensity_likelihood_prod_completed, Function.comp_def] using he

end CausalLowerbound.PartC

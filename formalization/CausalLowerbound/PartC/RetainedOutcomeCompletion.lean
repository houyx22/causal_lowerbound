import CausalLowerbound.PartC.UnitCubeGhosts
import CausalLowerbound.PartC.PhysicalLocalOutcomeMatching

/-! Cubic retained-site cells inside a full carrier configuration. Ghost
observation coefficients are zero, so their likelihoods are one. The
fourth-moment correction at ghost sites can therefore be chosen to match
their effective shifts without imposing any ghost assignment condition. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative RoughOutcome
variable {I G V d : Type*} [Fintype I] [Fintype G] [Fintype V] [Fintype d] [DecidableEq d]

theorem retainedOutcomePolynomial_completed (Q : ℕ) (e : I ⊕ G ≃ V) (R T : I → ℝ)
    (jb η rough offset ψ : V → ℝ) (sites : V → d → ℝ) :
    retainedOutcomePolynomial Q (completedSites e R (fun _ => 0)) (completedSites e T (fun _ => 0))
      jb η rough offset ψ sites =
      retainedOutcomePolynomial Q R T (fun i => jb (e (Sum.inl i))) (fun i => η (e (Sum.inl i)))
        (fun i => rough (e (Sum.inl i))) (fun i => offset (e (Sum.inl i)))
        (fun i => ψ (e (Sum.inl i))) (fun i => sites (e (Sum.inl i))) := by
  unfold retainedOutcomePolynomial
  rw [← e.prod_comp (fun j => outcomeCellPolynomial (completedSites e R (fun _ => 0) j)
    (completedSites e T (fun _ => 0) j) (jb j) (η j) (rough j)
    (retainedFieldPolynomial Q (offset j) (ψ j) (sites j)))]
  simp only [Fintype.prod_sum_type, completedSites_retained, completedSites_ghost]
  simp [outcomeCellPolynomial, outcomeSitePolynomial]

theorem outcome_likelihood_prod_completed (e : I ⊕ G ≃ V) (R T : I → ℝ)
    (jb η smooth rough : V → ℝ) :
    (∏ j, likelihood (completedSites e R (fun _ => 0) j) (completedSites e T (fun _ => 0) j)
      (jb j) (η j) (smooth j) (rough j)) =
      ∏ i, likelihood (R i) (T i) (jb (e (Sum.inl i))) (η (e (Sum.inl i)))
        (smooth (e (Sum.inl i))) (rough (e (Sum.inl i))) := by
  rw [← e.prod_comp (fun j => likelihood (completedSites e R (fun _ => 0) j)
    (completedSites e T (fun _ => 0) j) (jb j) (η j) (smooth j) (rough j))]
  simp only [Fintype.prod_sum_type, completedSites_retained, completedSites_ghost]
  simp [likelihood]

theorem outcome_real_prod_completed (e : I ⊕ G ≃ V) (R T : I → ℝ)
    (jb η smooth rough δ : V → ℝ) :
    (∏ j, (likelihood (completedSites e R (fun _ => 0) j) (completedSites e T (fun _ => 0) j)
      (jb j) (η j) (smooth j) (rough j) +
      realField (completedSites e R (fun _ => 0) j) (completedSites e T (fun _ => 0) j) (smooth j) (δ j))) =
      ∏ i, (likelihood (R i) (T i) (jb (e (Sum.inl i))) (η (e (Sum.inl i)))
        (smooth (e (Sum.inl i))) (rough (e (Sum.inl i))) +
        realField (R i) (T i) (smooth (e (Sum.inl i))) (δ (e (Sum.inl i)))) := by
  rw [← e.prod_comp (fun j => likelihood (completedSites e R (fun _ => 0) j)
    (completedSites e T (fun _ => 0) j) (jb j) (η j) (smooth j) (rough j) +
      realField (completedSites e R (fun _ => 0) j) (completedSites e T (fun _ => 0) j) (smooth j) (δ j))]
  simp only [Fintype.prod_sum_type, completedSites_retained, completedSites_ghost]
  simp [likelihood, realField]

theorem removed_physical_outcome_retained_matching [LinearOrder V]
    {Ω : Type*} [Fintype Ω] (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h) (x : V → d → ℝ)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (e : I ⊕ G ≃ V) (R T jitter : I → ℝ) (jb scale offset ψ : V → ℝ)
    (W : Representative.Array d V (activeBlocks (d := d) ℓ h) 3) (u : V × d → ℝ) (τ amp : ℝ)
    (hshift : ∀ i, coarseBump x₀ h (x (e (Sum.inl i))) = 0 ∨
      (ψ (e (Sum.inl i)) * amp) * scale (e (Sum.inl i)) = 0 ∨
      (ψ (e (Sum.inl i)) * amp) * scale (e (Sum.inl i)) = jitter i) :
    let keep : I → V := fun i => e (Sum.inl i)
    let B := remove (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) W
    let η := fun i => physicalRoughCorrection x₀ ℓ h (jitter i) (x (keep i))
    independentSigns.expect (fun ζ =>
      outcomeCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ
        (fun i => scale i ^ 2 * coarseBump x₀ h (x i) ^ 2) B u
        (fun i => scale i * physicalRoughField x₀ ℓ h ζ (x i)) ζ
        (retainedOutcomePolynomial Q R T (jb ∘ keep) η
          (fun i => physicalRoughField x₀ ℓ h ζ (x (keep i))) (offset ∘ keep) (ψ ∘ keep)
          (configurationSite u ∘ keep))) =
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) *
        μ.expect (fun ξ => independentSigns.expect (fun ζ =>
          pointValue (torusProjection u) (fun i => scale i * physicalRoughField x₀ ℓ h ζ (x i)) ζ B *
            ((∏ i, (likelihood (R i) (T i) (jb (keep i)) (η i)
              (offset (keep i) + ψ (keep i) * coefficientEvaluation (U ξ) (configurationSite u (keep i)))
                (physicalRoughField x₀ ℓ h ζ (x (keep i))) +
              realField (R i) (T i)
                (offset (keep i) + ψ (keep i) * coefficientEvaluation (U ξ) (configurationSite u (keep i)))
                (((ψ (keep i) * amp) * scale (keep i)) * jb (keep i) * coarseBump x₀ h (x (keep i)) ^ 2))) -
              ∏ i, likelihood (R i) (T i) (jb (keep i)) (η i)
                (offset (keep i) + ψ (keep i) * coefficientEvaluation (U ξ) (configurationSite u (keep i)))
                (physicalRoughField x₀ ℓ h ζ (x (keep i)))))) := by
  let auxJitter : V → ℝ := completedSites e jitter (fun g => (ψ (e (Sum.inr g)) * amp) * scale (e (Sum.inr g)))
  have haux (i : V) : coarseBump x₀ h (x i) = 0 ∨
      (ψ i * amp) * scale i = 0 ∨ (ψ i * amp) * scale i = auxJitter i := by
    obtain ⟨i, rfl⟩ := e.surjective i
    cases i with
    | inl i => simpa only [auxJitter, completedSites_retained] using hshift i
    | inr g => exact Or.inr (Or.inr (by simp only [auxJitter, completedSites_ghost]))
  have he := removed_physical_outcome_coefficient_matching Q hQ hcard μ U x₀ ℓ h hℓ hh x hsep
    (completedSites e R (fun _ => 0)) (completedSites e T (fun _ => 0)) jb auxJitter scale offset ψ W u τ amp haux
  simpa only [retainedOutcomePolynomial_completed, outcome_real_prod_completed,
    outcome_likelihood_prod_completed, Function.comp_def, auxJitter, completedSites_retained] using he

end CausalLowerbound.PartC

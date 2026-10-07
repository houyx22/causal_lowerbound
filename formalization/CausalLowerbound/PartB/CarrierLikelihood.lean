import CausalLowerbound.PartB.CarrierPolynomialMoments
import CausalLowerbound.PartB.LikelihoodPolynomials

/-! The positive carrier acts on the actual joint likelihood of a
component. This identifies the Q-site posterior effect with site jitters;
the remaining ghost integration is a separate measure-theoretic step. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped BigOperators
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener ConfigurationShells
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I Ω : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype Ω]

def retainedLikelihood (Q : ℕ) (side : Bool) (R T : I → ℝ) (a b : ℝ) (η δ offset ψ : I → ℝ)
    (sites : I → d → ℝ) (U : CoefficientExponent d Q → ℝ) : ℝ :=
  ∏ i, siteFieldLikelihood side (R i) (T i) a b (η i) (δ i)
    (offset i + ψ i * coefficientEvaluation U (sites i))

def jitteredRetainedLikelihood (Q : ℕ) (side : Bool) (R T : I → ℝ) (a b : ℝ)
    (η δ offset ψ : I → ℝ) (sites : I → d → ℝ) (U : CoefficientExponent d Q → ℝ)
    (t : ℝ) (ζ : I → ℝ) : ℝ :=
  ∏ i, siteFieldLikelihood side (R i) (T i) a b (η i) (δ i)
    (offset i + ψ i * (coefficientEvaluation U (sites i) + t * ζ i))

theorem retainedLikelihood_polynomial (Q : ℕ) (side : Bool) (R T : I → ℝ) (a b : ℝ)
    (η δ offset ψ : I → ℝ) (sites : I → d → ℝ) :
    ∃ L : MvPolynomial (CoefficientExponent d Q) ℝ,
      L.totalDegree ≤ 4 * Fintype.card I ∧
      ∀ U, MvPolynomial.eval U L = retainedLikelihood Q side R T a b η δ offset ψ sites U := by
  refine ⟨componentLikelihoodPolynomial side R T a b η δ
    (fun i => retainedFieldPolynomial Q (offset i) (ψ i) (sites i)),
    componentLikelihoodPolynomial_degree _ _ _ _ _ _ _ _
      (fun i => retainedFieldPolynomial_degree Q (offset i) (ψ i) (sites i)), ?_⟩
  intro U
  simp only [componentLikelihoodPolynomial_eval, retainedFieldPolynomial_eval, retainedLikelihood]

theorem retainedLikelihood_virtual_identity (Q : ℕ) (hQ : 0 < Q) (μ : FiniteLaw Ω)
    (U : Ω → CoefficientExponent d Q → ℝ) (u : Fin Q × d → ℝ) (ε t : ℝ)
    (side : Bool) (R T : I → ℝ) (a b : ℝ) (η δ offset ψ : I → ℝ) (keep : I → Fin Q) :
    graphTaper edgeLeft edgeRight taperCutoff ε (graphDistance edgeLeft edgeRight u) *
      ((μ.prod (independentSigns (ι := Fin Q))).expect (fun z =>
        retainedLikelihood Q side R T a b η δ offset ψ (fun i => configurationSite u (keep i))
          (virtualCoefficientShift (U z.1) u t (fun j => sign (z.2 j)))) -
        μ.expect (fun z => retainedLikelihood Q side R T a b η δ offset ψ
          (fun i => configurationSite u (keep i)) (U z))) =
    graphTaper edgeLeft edgeRight taperCutoff ε (graphDistance edgeLeft edgeRight u) *
      ((μ.prod (independentSigns (ι := Fin Q))).expect (fun z =>
        jitteredRetainedLikelihood Q side R T a b η δ offset ψ (fun i => configurationSite u (keep i))
          (U z.1) t (fun i => sign (z.2 (keep i)))) -
        μ.expect (fun z => retainedLikelihood Q side R T a b η δ offset ψ
          (fun i => configurationSite u (keep i)) (U z))) := by
  exact retained_virtual_moment Q hQ (by simp) μ U u ε t keep
    (fun i => configurationSite u (keep i)) (fun _ => rfl) ψ
    (fun v => ∏ i, siteFieldLikelihood side (R i) (T i) a b (η i) (δ i) (offset i + v i))

theorem paper_posterior_retained_likelihood (Q : ℕ) [NeZero Q] (hIQ : Fintype.card I ≤ Q)
    (ρ θ p B : ℝ) (hρ : 0 < ρ) (hθ : 0 < θ) (hθ1 : θ < 1) (hp : 0 < p)
    (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    ∀ᶠ n : ℕ in atTop, ∃ (H : DiscreteLaw ℕ)
      (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))),
      0 < H.weight 0 ∧ (∀ label z, 0 < (kernel label).weight z) ∧
      ∀ (u : Fin Q × d → ℝ) (keep : I → Fin Q) (side : Bool) (R T : I → ℝ)
        (a b : ℝ) (η δ offset ψ : I → ℝ),
        (coefficientPosterior H kernel Q θ hθ.le hθ1
          (fun j => torusProjection (configurationSite u j))).expect
            (fun z => retainedLikelihood Q side R T a b η δ offset ψ
              (fun i => configurationSite u (keep i)) (paperCoefficientAtoms Q ρ z)) -
        (paperCoefficientLaw Q).expect (fun z => retainedLikelihood Q side R T a b η δ offset ψ
          (fun i => configurationSite u (keep i)) (paperCoefficientAtoms Q ρ z)) =
        graphTaper edgeLeft edgeRight taperCutoff (logarithmicThreshold p B (n + 1))
          (graphDistance edgeLeft edgeRight u) *
          (((paperCoefficientLaw Q).prod (independentSigns (ι := Fin Q))).expect (fun z =>
            jitteredRetainedLikelihood Q side R T a b η δ offset ψ
              (fun i => configurationSite u (keep i)) (paperCoefficientAtoms Q ρ z.1)
              (polynomialAmplitude p (n + 1)) (fun i => sign (z.2 (keep i)))) -
          (paperCoefficientLaw Q).expect (fun z => retainedLikelihood Q side R T a b η δ offset ψ
            (fun i => configurationSite u (keep i)) (paperCoefficientAtoms Q ρ z))) := by
  filter_upwards [paper_posterior_polynomial_interpolation (d := d) Q ρ θ p B hρ hθ hθ1 hp hB] with n hn
  obtain ⟨H, kernel, h0, hk, hm⟩ := hn
  refine ⟨H, kernel, h0, hk, ?_⟩
  intro u keep side R T a b η δ offset ψ
  obtain ⟨L, hL, heval⟩ := retainedLikelihood_polynomial Q side R T a b η δ offset ψ
    (fun i => configurationSite u (keep i))
  have h := hm u L (hL.trans (Nat.mul_le_mul_left 4 hIQ))
  simp_rw [heval] at h
  exact h.trans (retainedLikelihood_virtual_identity Q (NeZero.pos Q) _ _ u _ _ side R T a b η δ offset ψ keep)

end CausalLowerbound.PartB.ShellGeometry

import CausalLowerbound.PartB.EvaluatedCarrier

/-! One carrier and one coefficient kernel work simultaneously for all
retained block sizes and all component likelihoods. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Filter
open scoped BigOperators Classical
universe v w
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener ConfigurationShells
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def PolynomialPosteriorInterpolation (Q : ℕ) (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (ρ θ ε t : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) : Prop :=
  ∀ (u : Fin Q × d → ℝ) (L : MvPolynomial (CoefficientExponent d Q) ℝ),
    L.totalDegree ≤ 4 * Q →
      (coefficientPosterior H kernel Q θ hθ hθ1 (fun i => torusProjection (configurationSite u i))).expect
        (fun z => MvPolynomial.eval (paperCoefficientAtoms Q ρ z) L) -
      (paperCoefficientLaw Q).expect (fun z => MvPolynomial.eval (paperCoefficientAtoms Q ρ z) L) =
      completeTaper Q ε u *
        (((paperCoefficientLaw Q).prod (independentSigns (ι := Fin Q))).expect (fun z =>
          MvPolynomial.eval (virtualCoefficientShift (paperCoefficientAtoms Q ρ z.1) u t
            (fun i => sign (z.2 i))) L) -
          (paperCoefficientLaw Q).expect (fun z => MvPolynomial.eval (paperCoefficientAtoms Q ρ z) L))

def EvaluatedPosteriorInterpolation (Q : ℕ) (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (ρ θ ε t : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    {K : Type v} {G : Type w} [Fintype K] [Fintype G] (e : K ⊕ G ≃ Fin Q) : Prop :=
  ∀ (u : K → d → ℝ) (side : Bool) (R T : K → ℝ) (a b : ℝ) (η δ offset ψ : K → ℝ),
    let f := fun z => retainedLikelihood Q side R T a b η δ offset ψ u (paperCoefficientAtoms Q ρ z)
    let χ := ghostActivation H Q θ (completedTorusTaper Q e ε) (fun i => torusProjection (u i))
    (coefficientPosterior H kernel Q θ hθ hθ1 (fun i => torusProjection (u i))).expect f -
      (paperCoefficientLaw Q).expect f = χ *
        (((paperCoefficientLaw Q).prod (independentSigns (ι := Fin Q))).expect (fun z =>
          jitteredRetainedLikelihood Q side R T a b η δ offset ψ u (paperCoefficientAtoms Q ρ z.1)
            t (fun i => sign (z.2 (e (Sum.inl i))))) - (paperCoefficientLaw Q).expect f)

theorem polynomial_to_evaluated_likelihood (Q : ℕ) [NeZero Q] (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (ρ θ ε t : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : PolynomialPosteriorInterpolation Q H kernel ρ θ ε t hθ hθ1)
    {K : Type v} {G : Type w} [Fintype K] [Fintype G] (e : K ⊕ G ≃ Fin Q) :
    EvaluatedPosteriorInterpolation Q H kernel ρ θ ε t hθ hθ1 e := by
  have hK : Fintype.card K ≤ Q := by
    have hc := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    omega
  intro u side R T a b η δ offset ψ
  dsimp only
  let f := fun z => retainedLikelihood Q side R T a b η δ offset ψ u (paperCoefficientAtoms Q ρ z)
  let up := fun i => torusProjection (u i)
  rw [← coefficientPosterior_constant_expect H (paperCoefficientLaw Q) Q θ hθ hθ1 up f]
  apply coefficientPosterior_ghost_interpolation
  intro z
  rw [coefficientPosterior_constant_expect]
  let v := completedRealConfiguration Q e u z
  let keep := fun i => e (Sum.inl i)
  obtain ⟨L, hL, heval⟩ := retainedLikelihood_polynomial Q side R T a b η δ offset ψ
    (fun i => configurationSite v (keep i))
  have hh := hm v L (hL.trans (Nat.mul_le_mul_left 4 hK))
  simp_rw [heval] at hh
  have hj := retainedLikelihood_virtual_identity Q (NeZero.pos Q) (paperCoefficientLaw Q)
    (paperCoefficientAtoms Q ρ) v ε t side R T a b η δ offset ψ keep
  have h := hh.trans hj
  dsimp only [v, keep] at h
  simp_rw [completedRealConfiguration_keep] at h
  rw [completedRealConfiguration_projection] at h
  have hr := coefficientPosterior_difference_equiv H (fun _ => paperCoefficientLaw Q)
    kernel Q θ hθ hθ1 e.symm (Sum.elim up z) f
  simp_rw [coefficientPosterior_constant_expect] at hr
  rw [← hr]
  change _ = completedTorusTaper Q e ε (up, z) * _
  rw [← completedRealConfiguration_taper, coefficientPosterior_constant_expect]
  exact h

theorem paper_uniform_evaluated_likelihood (Q : ℕ) [NeZero Q] (ρ θ p B : ℝ)
    (hρ : 0 < ρ) (hθ : 0 < θ) (hθ1 : θ < 1) (hp : 0 < p)
    (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    ∀ᶠ n : ℕ in atTop, ∃ (H : DiscreteLaw ℕ)
      (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))),
      0 < H.weight 0 ∧ (∀ label z, 0 < (kernel label).weight z) ∧
      ∀ (K : Type v) (G : Type w) [Fintype K] [Fintype G] (e : K ⊕ G ≃ Fin Q),
        EvaluatedPosteriorInterpolation Q H kernel ρ θ
          (logarithmicThreshold p B (n + 1)) (polynomialAmplitude p (n + 1)) hθ.le hθ1 e := by
  filter_upwards [paper_posterior_polynomial_interpolation (d := d) Q ρ θ p B hρ hθ hθ1 hp hB] with n hn
  obtain ⟨H, kernel, h0, hk, hm⟩ := hn
  refine ⟨H, kernel, h0, hk, ?_⟩
  intro K G _ _ e
  exact polynomial_to_evaluated_likelihood Q H kernel ρ θ _ _ hθ.le hθ1 hm e

end CausalLowerbound.PartB.ShellGeometry

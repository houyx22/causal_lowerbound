import CausalLowerbound.PartB.BlockActivation
import CausalLowerbound.AdditiveTensorization

/-! The genuine many-block partial-activation identity. All block effects
are summed before the likelihood is evaluated, so overlapping blocks and
shared observations retain their original dependence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Filter
open scoped BigOperators Classical
universe uI uK uG
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {I : Type uI} {K : Type uK} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

def ComponentActivationIdentity (Q : ℕ) (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (ρ θ ε t : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : K → Finset I)
    {G : K → Type uG} [∀ k, Fintype (G k)] (e : ∀ k, S k ⊕ G k ≃ Fin Q)
    (u : K → I → d → ℝ) (ψ : K → I → ℝ) : Prop :=
  ∀ (side : Bool) (R T : I → ℝ) (a b : ℝ) (η δ : I → ℝ),
    (FiniteLaw.independent (fun k => coefficientPosterior H kernel Q θ hθ hθ1
      (fun i : S k => torusProjection (u k i.val)))).expect
        (fun z => jointFieldLikelihood side R T a b η δ
          (fun i => ∑ k, baselineBlockField Q ρ (u k) (ψ k) (z k) i)) =
    (FiniteLaw.independent (fun k => evaluatedBlockActivation H Q θ ε hθ hθ1 (S k) (e k) (u k))).expect
      (fun active => (FiniteLaw.independent (fun _ : K =>
        (paperCoefficientLaw Q).prod (independentSigns (ι := Fin Q)))).expect
          (fun z => jointFieldLikelihood side R T a b η δ
            (fun i => ∑ k, activatedBlockField Q ρ t (S k) (e k) (u k) (ψ k) (active k, z k) i)))

theorem component_activation_of_evaluated (Q : ℕ) (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (ρ θ ε t : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : K → Finset I)
    {G : K → Type uG} [∀ k, Fintype (G k)] (e : ∀ k, S k ⊕ G k ≃ Fin Q)
    (u : K → I → d → ℝ) (ψ : K → I → ℝ) (hψ : ∀ k i, i ∉ S k → ψ k i = 0)
    (hm : ∀ k, EvaluatedPosteriorInterpolation Q H kernel ρ θ ε t hθ hθ1 (e k)) :
    ComponentActivationIdentity Q H kernel ρ θ ε t hθ hθ1 S e u ψ := by
  intro side R T a b η δ
  have he := FiniteLaw.independent_additive_replacement
    (fun k => coefficientPosterior H kernel Q θ hθ hθ1 (fun i : S k => torusProjection (u k i.val)))
    (fun k => (evaluatedBlockActivation H Q θ ε hθ hθ1 (S k) (e k) (u k)).prod
      ((paperCoefficientLaw Q).prod (independentSigns (ι := Fin Q))))
    (fun k => baselineBlockField Q ρ (u k) (ψ k))
    (fun k => activatedBlockField Q ρ t (S k) (e k) (u k) (ψ k))
    (jointFieldLikelihood side R T a b η δ)
    (fun k offset => evaluated_block_activation Q (S k) (e k) H kernel ρ θ ε t hθ hθ1
      (hm k) (u k) side R T a b η δ offset (ψ k) (hψ k))
  exact he.trans (FiniteLaw.expect_independent_prods _ _ _)

/-- The carrier is constructed once and works for every finite component
and every family of incident blocks with at most Q sites per block. -/
theorem paper_component_activation (Q : ℕ) [NeZero Q] (ρ θ p B : ℝ)
    (hρ : 0 < ρ) (hθ : 0 < θ) (hθ1 : θ < 1) (hp : 0 < p)
    (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    ∀ᶠ n : ℕ in atTop, ∃ (H : DiscreteLaw ℕ)
      (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))),
      0 < H.weight 0 ∧ (∀ label z, 0 < (kernel label).weight z) ∧
      ∀ (I : Type uI) (K : Type uK) [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
        (S : K → Finset I) (G : K → Type uG) [∀ k, Fintype (G k)] (e : ∀ k, S k ⊕ G k ≃ Fin Q)
        (u : K → I → d → ℝ) (ψ : K → I → ℝ),
        (∀ k i, i ∉ S k → ψ k i = 0) →
        ComponentActivationIdentity Q H kernel ρ θ (logarithmicThreshold p B (n + 1))
          (polynomialAmplitude p (n + 1)) hθ.le hθ1 S e u ψ := by
  filter_upwards [paper_uniform_evaluated_likelihood (d := d) Q ρ θ p B hρ hθ hθ1 hp hB] with n hn
  obtain ⟨H, kernel, h0, hk, hm⟩ := hn
  refine ⟨H, kernel, h0, hk, ?_⟩
  intro I K _ _ _ _ S G _ e u ψ hψ
  exact component_activation_of_evaluated Q H kernel ρ θ _ _ hθ.le hθ1 S e u ψ hψ
    (fun k => hm (S k) (G k) (e k))

end CausalLowerbound.PartB.ShellGeometry

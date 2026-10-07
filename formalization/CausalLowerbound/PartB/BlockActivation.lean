import CausalLowerbound.PartB.BlockLikelihood

/-! The one-block likelihood identity as an actual Bernoulli activation
expectation, with its probability constructed by the ghost integral. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace CausalLowerbound.PartB

theorem activationLaw_expect (χ : ℝ) (h0 : 0 ≤ χ) (h1 : χ ≤ 1) (f : Bool → ℝ) :
    (activationLaw χ h0 h1).expect f = (1 - χ) * f false + χ * f true := by
  simp [FiniteLaw.expect, activationLaw, Fintype.sum_bool, add_comm]

namespace ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I] [Fintype G]

def evaluatedBlockWeight (H : DiscreteLaw ℕ) (Q : ℕ) (θ ε : ℝ) (S : Finset I)
    (e : S ⊕ G ≃ Fin Q) (u : I → d → ℝ) : ℝ :=
  ghostActivation H Q θ (completedTorusTaper Q e ε) (fun i : S => torusProjection (u i.val))

theorem evaluatedBlockWeight_bounds (H : DiscreteLaw ℕ) (Q : ℕ) (θ ε : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : Finset I) (e : S ⊕ G ≃ Fin Q) (u : I → d → ℝ) :
    0 ≤ evaluatedBlockWeight H Q θ ε S e u ∧ evaluatedBlockWeight H Q θ ε S e u ≤ 1 :=
  ghostActivation_bounds H Q θ hθ hθ1 (completedTorusTaper Q e ε)
    (completedTorusTaper_continuous Q e ε) (completedTorusTaper_bounds Q e ε) _

def evaluatedBlockActivation (H : DiscreteLaw ℕ) (Q : ℕ) (θ ε : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : Finset I) (e : S ⊕ G ≃ Fin Q) (u : I → d → ℝ) : FiniteLaw Bool :=
  activationLaw (evaluatedBlockWeight H Q θ ε S e u)
    (evaluatedBlockWeight_bounds H Q θ ε hθ hθ1 S e u).1
    (evaluatedBlockWeight_bounds H Q θ ε hθ hθ1 S e u).2

def baselineBlockField (Q : ℕ) (ρ : ℝ) (u : I → d → ℝ) (ψ : I → ℝ)
    (z : MomentGrid (CoefficientExponent d Q) (4 * Q)) (i : I) : ℝ :=
  ψ i * coefficientEvaluation (paperCoefficientAtoms Q ρ z) (u i)

def activatedBlockField (Q : ℕ) (ρ t : ℝ) (S : Finset I) (e : S ⊕ G ≃ Fin Q)
    (u : I → d → ℝ) (ψ : I → ℝ)
    (z : Bool × (MomentGrid (CoefficientExponent d Q) (4 * Q) × (Fin Q → Bool))) (i : I) : ℝ :=
  ψ i * (coefficientEvaluation (paperCoefficientAtoms Q ρ z.2.1) (u i) +
    if z.1 then t * retainedSigns Q S e z.2.2 i else 0)

theorem evaluated_block_activation (Q : ℕ) (S : Finset I) (e : S ⊕ G ≃ Fin Q)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (ρ θ ε t : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : EvaluatedPosteriorInterpolation Q H kernel ρ θ ε t hθ hθ1 e)
    (u : I → d → ℝ) (side : Bool) (R T : I → ℝ) (a b : ℝ) (η δ offset ψ : I → ℝ)
    (hψ : ∀ i, i ∉ S → ψ i = 0) :
    (coefficientPosterior H kernel Q θ hθ hθ1 (fun i : S => torusProjection (u i.val))).expect
      (fun z => jointFieldLikelihood side R T a b η δ (fun i => offset i + baselineBlockField Q ρ u ψ z i)) =
    ((evaluatedBlockActivation H Q θ ε hθ hθ1 S e u).prod
      ((paperCoefficientLaw Q).prod (independentSigns (ι := Fin Q)))).expect
        (fun z => jointFieldLikelihood side R T a b η δ (fun i => offset i + activatedBlockField Q ρ t S e u ψ z i)) := by
  have hh := evaluated_block_likelihood Q S e H kernel ρ θ ε t hθ hθ1 hm u side R T a b η δ offset ψ hψ
  dsimp only at hh
  rw [FiniteLaw.expect_prod, evaluatedBlockActivation, activationLaw_expect]
  simp only [activatedBlockField, Bool.false_eq_true, if_false, if_true, add_zero]
  simp_rw [FiniteLaw.expect_prod, FiniteLaw.expect_const]
  rw [FiniteLaw.expect_prod] at hh
  dsimp only [baselineBlockField, evaluatedBlockWeight]
  linear_combination hh

end ShellGeometry
end CausalLowerbound.PartB

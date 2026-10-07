import CausalLowerbound.PartB.UniformEvaluatedCarrier
import CausalLowerbound.FinitePushforward
import CausalLowerbound.PartB.ComponentMixture

/-! Extension of the evaluated one-block identity to a whole component,
including sites outside the block where its packet is zero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I] [Fintype G]

def jointFieldLikelihood (side : Bool) (R T : I → ℝ) (a b : ℝ) (η δ z : I → ℝ) : ℝ :=
  ∏ i, siteFieldLikelihood side (R i) (T i) a b (η i) (δ i) (z i)

def retainedSigns (Q : ℕ) (S : Finset I) (e : S ⊕ G ≃ Fin Q) (ζ : Fin Q → Bool) (i : I) : ℝ :=
  if hi : i ∈ S then sign (ζ (e (Sum.inl ⟨i, hi⟩))) else 0

theorem retainedSigns_mem (Q : ℕ) (S : Finset I) (e : S ⊕ G ≃ Fin Q) (ζ : Fin Q → Bool) (i : S) :
    retainedSigns Q S e ζ i.val = sign (ζ (e (Sum.inl i))) := by
  simp [retainedSigns, i.property]

theorem jointFieldLikelihood_restrict (S : Finset I) (side : Bool) (R T : I → ℝ) (a b : ℝ)
    (η δ offset ψ v : I → ℝ) (hψ : ∀ i, i ∉ S → ψ i = 0) :
    jointFieldLikelihood side R T a b η δ (fun i => offset i + ψ i * v i) =
      (∏ i : S, siteFieldLikelihood side (R i.val) (T i.val) a b (η i.val) (δ i.val)
        (offset i.val + ψ i.val * v i.val)) *
      ∏ i : {i // i ∉ S}, siteFieldLikelihood side (R i.val) (T i.val) a b (η i.val) (δ i.val) (offset i.val) := by
  unfold jointFieldLikelihood
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
  apply congrArg₂ (fun x y : ℝ => x * y)
  · have hinst : Subtype.fintype (fun i : I => i ∈ S) = Finset.Subtype.fintype S :=
      Subsingleton.elim _ _
    simp only [hinst]
  · apply Fintype.prod_equiv (Equiv.refl _) _ _
    intro i
    dsimp only [Equiv.refl_apply]
    rw [hψ i.val i.property, zero_mul, add_zero]

theorem evaluated_block_likelihood (Q : ℕ) (S : Finset I) (e : S ⊕ G ≃ Fin Q)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (ρ θ ε t : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : EvaluatedPosteriorInterpolation Q H kernel ρ θ ε t hθ hθ1 e)
    (u : I → d → ℝ) (side : Bool) (R T : I → ℝ) (a b : ℝ) (η δ offset ψ : I → ℝ)
    (hψ : ∀ i, i ∉ S → ψ i = 0) :
    let ν := coefficientPosterior H kernel Q θ hθ hθ1 (fun i : S => torusProjection (u i.val))
    let χ := ghostActivation H Q θ (completedTorusTaper Q e ε) (fun i : S => torusProjection (u i.val))
    let baseline := fun z => jointFieldLikelihood side R T a b η δ
      (fun i => offset i + ψ i * coefficientEvaluation (paperCoefficientAtoms Q ρ z) (u i))
    ν.expect baseline - (paperCoefficientLaw Q).expect baseline = χ *
      (((paperCoefficientLaw Q).prod (independentSigns (ι := Fin Q))).expect (fun z =>
        jointFieldLikelihood side R T a b η δ (fun i => offset i + ψ i *
          (coefficientEvaluation (paperCoefficientAtoms Q ρ z.1) (u i) + t * retainedSigns Q S e z.2 i))) -
        (paperCoefficientLaw Q).expect baseline) := by
  have hh := hm (fun i : S => u i.val) side (fun i => R i.val) (fun i => T i.val) a b
    (fun i => η i.val) (fun i => δ i.val) (fun i => offset i.val) (fun i => ψ i.val)
  dsimp only at hh ⊢
  simp_rw [jointFieldLikelihood_restrict S side R T a b η δ offset ψ _ hψ,
    FiniteLaw.expect_mul_const]
  simp_rw [retainedSigns_mem]
  change _ - _ = _ * (_ - _) at hh
  unfold retainedLikelihood jitteredRetainedLikelihood at hh
  linear_combination (∏ i : {i // i ∉ S},
    siteFieldLikelihood side (R i.val) (T i.val) a b (η i.val) (δ i.val) (offset i.val)) * hh

end CausalLowerbound.PartB.ShellGeometry

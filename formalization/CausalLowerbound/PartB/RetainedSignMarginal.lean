import CausalLowerbound.PartB.BlockLikelihood
import CausalLowerbound.FiniteReindex
import CausalLowerbound.AdditiveTensorization

/-! The retained signs of each completed block have exactly the required
independent site marginal. Ghost signs contribute total mass one. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {I G K : Type*} [Fintype I] [DecidableEq I] [Fintype G] [Fintype K] [DecidableEq K]

theorem retained_sign_expect (Q : ℕ) (S : Finset I) (e : S ⊕ G ≃ Fin Q)
    (ψ : I → ℝ) (hψ : ∀ i, i ∉ S → ψ i = 0) (f : (I → ℝ) → ℝ) :
    (independentSigns (ι := Fin Q)).expect (fun ζ => f (fun i => ψ i * retainedSigns Q S e ζ i)) =
      (independentSigns (ι := I)).expect (fun ζ => f (fun i => ψ i * sign (ζ i))) := by
  letI : Fintype S := Subtype.fintype (fun i : I => i ∈ S)
  let g : (S → Bool) → ℝ := fun ζ => f (fun i => if hi : i ∈ S then ψ i * sign (ζ ⟨i, hi⟩) else 0)
  have hl : (independentSigns (ι := Fin Q)).expect
      (fun ζ => f (fun i => ψ i * retainedSigns Q S e ζ i)) =
      (independentSigns (ι := S)).expect g := by
    unfold independentSigns
    rw [FiniteLaw.expect_independent_equiv e (fun _ => rademacher)]
    have he : (fun _ : S ⊕ G => rademacher) =
        Sum.elim (fun _ : S => rademacher) (fun _ : G => rademacher) := by
      funext j
      cases j <;> rfl
    rw [he, FiniteLaw.expect_independent_sum]
    have hf (ζ : S → Bool) (ghost : G → Bool) :
        f (fun i => ψ i * retainedSigns Q S e (fun j => Sum.elim ζ ghost (e.symm j)) i) = g ζ := by
      congr 1
      funext i
      by_cases hi : i ∈ S <;> simp [retainedSigns, g, hi]
    simp_rw [hf, FiniteLaw.expect_const]
  have hr := FiniteLaw.expect_independent_subtype (fun _ : I => rademacher) (fun i => i ∈ S) g
  have hf (ζ : I → Bool) : g (fun i => ζ i.val) = f (fun i => ψ i * sign (ζ i)) := by
    dsimp only [g]
    congr 1
    funext i
    by_cases hi : i ∈ S
    · simp [hi]
    · simp [hi, hψ i hi]
  simp only [hf] at hr
  rw [hl]
  exact hr.symm

theorem retained_signs_additive (Q : ℕ) (S : K → Finset I)
    {G : K → Type*} [∀ k, Fintype (G k)] (e : ∀ k, S k ⊕ G k ≃ Fin Q)
    (ψ : K → I → ℝ) (hψ : ∀ k i, i ∉ S k → ψ k i = 0) (f : (I → ℝ) → ℝ) :
    (FiniteLaw.independent (fun _ : K => independentSigns (ι := Fin Q))).expect
      (fun ζ => f (fun i => ∑ k, ψ k i * retainedSigns Q (S k) (e k) (ζ k) i)) =
    (FiniteLaw.independent (fun _ : I => independentSigns (ι := K))).expect
      (fun ζ => f (fun i => ∑ k, ψ k i * sign (ζ i k))) := by
  have he := FiniteLaw.independent_additive_replacement
    (fun _ : K => independentSigns (ι := Fin Q)) (fun _ : K => independentSigns (ι := I))
    (fun k ζ i => ψ k i * retainedSigns Q (S k) (e k) ζ i)
    (fun k ζ i => ψ k i * sign (ζ i)) f
    (fun k offset => retained_sign_expect Q (S k) (e k) (ψ k) (hψ k)
      (fun v => f (fun i => offset i + v i)))
  exact he.trans (FiniteLaw.expect_independent_transpose (fun (_k : K) (_i : I) => rademacher) _)

end CausalLowerbound.PartB.ShellGeometry

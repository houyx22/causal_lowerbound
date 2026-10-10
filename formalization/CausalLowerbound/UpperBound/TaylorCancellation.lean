import CausalLowerbound.UpperBound.CompletedStencil
import CausalLowerbound.UpperBound.FrechetTaylor

/-! The tensor stencil annihilates every Taylor polynomial of total degree
at most p.  Expanding multilinear maps in the coordinate basis proves this
without any additional differentiability or mixed-derivative assumptions. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

def wordIndex (p : ℕ) {k : ℕ} (s : Fin k → d) (hkp : k ≤ p) : TensorIndex d p :=
  fun i => ⟨(Finset.univ.filter (fun a => s a = i)).card, by
    apply Nat.lt_succ_of_le
    exact (Finset.card_filter_le _ _).trans (by simpa using hkp)⟩

theorem tensorMonomial_wordIndex (p : ℕ) {k : ℕ} (s : Fin k → d)
    (hkp : k ≤ p) (x : d → ℝ) :
    tensorMonomial p (wordIndex p s hkp) x = ∏ a, x (s a) := by
  simpa only [tensorMonomial, wordIndex, Finset.prod_const] using
    Finset.prod_fiberwise' Finset.univ s x

theorem coordinate_basis_expansion (x : d → ℝ) :
    x = ∑ i, x i • (Pi.single i 1 : d → ℝ) := by
  ext j
  simp [Pi.single_apply, Finset.sum_apply]

theorem multilinear_coordinate_expansion {k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => d → ℝ) ℝ) (x : d → ℝ) :
    A (fun _ => x) = ∑ s : Fin k → d,
      (∏ a, x (s a)) * A (fun a => Pi.single (s a) 1) := by
  calc
    _ = A (fun _ => ∑ i, x i • (Pi.single i 1 : d → ℝ)) :=
      congrArg A (funext (fun _ => coordinate_basis_expansion x))
    _ = _ := by
      rw [A.map_sum]
      apply Finset.sum_congr rfl
      intro s _
      exact A.map_smul_univ (fun a => x (s a)) (fun a => Pi.single (s a) 1)

theorem multilinear_cancel_of_monomial_cancel {I : Type*} [Fintype I]
    (p : ℕ) (w : I → ℝ) (z : I → d → ℝ)
    (hc : ∀ ν : TensorIndex d p, ∑ i, w i * tensorMonomial p ν (z i) = 0)
    {k : ℕ} (hkp : k ≤ p)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => d → ℝ) ℝ) :
    ∑ i, w i * A (fun _ => z i) = 0 := by
  simp_rw [multilinear_coordinate_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro s _
  simp_rw [← tensorMonomial_wordIndex p s hkp, ← mul_assoc]
  rw [← Finset.sum_mul, hc, zero_mul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem frechetTaylor_cancel_of_monomial_cancel {I : Type*} [Fintype I]
    (p q : ℕ) (hqp : q ≤ p) (w : I → ℝ) (z : I → d → ℝ)
    (hc : ∀ ν : TensorIndex d p, ∑ i, w i * tensorMonomial p ν (z i) = 0)
    (f : E → ℝ) (x : E) (L : (d → ℝ) →L[ℝ] E) :
    ∑ i, w i * frechetTaylor f q x (x + L (z i)) = 0 := by
  simp only [frechetTaylor, add_sub_cancel_left, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  have hkp : k ≤ p := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans hqp
  have he := multilinear_cancel_of_monomial_cancel p w z hc hkp
    ((iteratedFDeriv ℝ k f x).compContinuousLinearMap (fun _ => L))
  change ∑ i, w i * iteratedFDeriv ℝ k f x (fun _ => L (z i)) = 0 at he
  calc
    _ = (k.factorial : ℝ)⁻¹ *
        (∑ i, w i * iteratedFDeriv ℝ k f x (fun _ => L (z i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [he, mul_zero]

def tensorStencilNode (p : ℕ) (z : TensorIndex d p → d → ℝ) (v : d → ℝ) :
    Option (Option (TensorIndex d p)) → d → ℝ := Option.elim' v (Option.elim' 0 z)

theorem tensorContrastWeights_sum_monomial (p : ℕ)
    (z : TensorIndex d p → d → ℝ) (v : d → ℝ)
    (hz : IsUnit (tensorEvaluation p z).det) (ν : TensorIndex d p) :
    ∑ i, tensorContrastWeights p z v i * tensorMonomial p ν (tensorStencilNode p z v i) = 0 := by
  have he := tensorContrastWeights_cancel p z v hz ν
  simp only [Fintype.sum_option, tensorStencilNode, Option.elim'_none, Option.elim'_some]
  linarith

theorem tensorContrastWeights_cancel_taylor (p q : ℕ) (hqp : q ≤ p)
    (z : TensorIndex d p → d → ℝ) (v : d → ℝ)
    (hz : IsUnit (tensorEvaluation p z).det)
    (f : E → ℝ) (x : E) (L : (d → ℝ) →L[ℝ] E) :
    ∑ i, tensorContrastWeights p z v i *
      frechetTaylor f q x (x + L (tensorStencilNode p z v i)) = 0 :=
  frechetTaylor_cancel_of_monomial_cancel p q hqp _ _
    (tensorContrastWeights_sum_monomial p z v hz) f x L

end CausalLowerbound.UpperBound

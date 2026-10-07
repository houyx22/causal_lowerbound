import CausalLowerbound.PartC.RetainedOutcomeRows
import CausalLowerbound.PartC.BlockCoefficientShift

/-! Insert the incident observation variables into a completed carrier.
Nonincident variables are set to zero, while the inserted monomial has
degree zero at every ghost. All identities include empty retained sets. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial
variable {I V G : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [DecidableEq V] [Fintype G]

def retainedPolynomialMap (P : I → Prop) (e : {i // P i} ⊕ G ≃ V) :
    MvPolynomial I ℝ →ₐ[ℝ] MvPolynomial V ℝ :=
  aeval (fun i => if hi : P i then X (e (Sum.inl ⟨i, hi⟩)) else 0)

def retainedExponent (P : I → Prop) (e : {i // P i} ⊕ G ≃ V) (m : I →₀ ℕ) : V →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (completedSites e (fun i => m i.val) (fun _ => 0))

@[simp] theorem retainedExponent_retained (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (m : I →₀ ℕ) (i : {i // P i}) : retainedExponent P e m (e (Sum.inl i)) = m i.val := by
  simp [retainedExponent]

@[simp] theorem retainedExponent_ghost (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (m : I →₀ ℕ) (j : G) : retainedExponent P e m (e (Sum.inr j)) = 0 := by
  simp [retainedExponent]

theorem retainedExponent_degree_iff (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (m : I →₀ ℕ) (hoff : ∀ i, ¬P i → m i = 0) :
    (∀ v, retainedExponent P e m v ≤ 3) ↔ ∀ i, m i ≤ 3 := by
  constructor
  · intro he i
    by_cases hi : P i
    · simpa only [retainedExponent_retained] using he (e (Sum.inl ⟨i, hi⟩))
    · rw [hoff i hi]
      exact Nat.zero_le _
  · intro hm v
    obtain ⟨z, rfl⟩ := e.surjective v
    cases z with
    | inl i => simpa only [retainedExponent_retained] using hm i.val
    | inr j => simp only [retainedExponent_ghost, Nat.zero_le]

theorem retainedPolynomialMap_eval (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (p : MvPolynomial I ℝ) (z : V → ℝ) :
    eval z (retainedPolynomialMap P e p) =
      eval (fun i => if hi : P i then z (e (Sum.inl ⟨i, hi⟩)) else 0) p := by
  rw [retainedPolynomialMap, eval_aeval_polynomial]
  apply congrArg (fun f : I → ℝ => eval f p)
  funext i
  by_cases hi : P i
  · simp only [dif_pos hi, eval_X]
  · simp only [dif_neg hi, map_zero]

theorem retainedPolynomialMap_monomial (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (m : I →₀ ℕ) :
    retainedPolynomialMap P e (monomial m 1) =
      if ∀ i, ¬P i → m i = 0 then monomial (retainedExponent P e m) 1 else 0 := by
  by_cases hm : ∀ i, ¬P i → m i = 0
  · rw [if_pos hm]
    apply MvPolynomial.funext
    intro z
    rw [retainedPolynomialMap_eval, eval_monomial, eval_monomial]
    simp only [one_mul]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    let f := fun i => (if hi : P i then z (e (Sum.inl ⟨i, hi⟩)) else 0) ^ m i
    have hret (i : {i // P i}) : f i.val = z (e (Sum.inl i)) ^ m i.val := by
      simp only [f, dif_pos i.property]
    have hout (i : {i // ¬P i}) : f i.val = 1 := by
      simp only [f, hm i.val i.property, pow_zero]
    change (∏ i, f i) = _
    rw [← Fintype.prod_subtype_mul_prod_subtype P f,
      ← e.prod_comp (fun v => z v ^ retainedExponent P e m v)]
    simp only [hret, hout, Finset.prod_const_one, mul_one, Fintype.prod_sum_type,
      retainedExponent_retained, retainedExponent_ghost, pow_zero]
  · rw [if_neg hm]
    push_neg at hm
    obtain ⟨i, hi, hmi⟩ := hm
    apply MvPolynomial.funext
    intro z
    rw [retainedPolynomialMap_eval, eval_monomial, map_zero, one_mul]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [dif_neg hi, zero_pow hmi]

end CausalLowerbound.PartC

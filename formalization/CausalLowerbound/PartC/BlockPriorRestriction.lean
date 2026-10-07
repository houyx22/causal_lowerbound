import CausalLowerbound.DiscreteGrouping
import CausalLowerbound.FiniteReindex
import CausalLowerbound.PartC.SharedPolynomialMoments

/-! Restrict an actual shared-sign block prior to a subset of blocks.
The unused countable labels and conditional coefficient draws integrate
to one, even when their kernels depend on the retained shared signs. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.DiscreteLaw
variable {K L : Type*} [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]

theorem expect_independent_equiv (e : L ≃ K) (μ : K → DiscreteLaw ℕ) (f : (K → ℕ) → ℝ) :
    (independent μ).expect f =
      (independent (fun k => μ (e k))).expect (fun x => f (fun k => x (e.symm k))) := by
  unfold expect
  rw [← (Equiv.arrowCongr e (Equiv.refl ℕ)).tsum_eq]
  apply tsum_congr
  intro x
  have hw : (independent μ).weight ((Equiv.arrowCongr e (Equiv.refl ℕ)) x) =
      (independent (fun k => μ (e k))).weight x := by
    simp only [independent_weight]
    rw [← e.prod_comp]
    simp
  rw [hw]
  rfl

theorem expect_independent_sum_left (μ : K → DiscreteLaw ℕ) (ν : L → DiscreteLaw ℕ)
    (f : (K → ℕ) → ℝ) (B : ℝ) (hf : ∀ x, |f x| ≤ B) :
    (independent (Sum.elim μ ν)).expect (fun x => f (fun k => x (Sum.inl k))) =
      (independent μ).expect f := by
  let e := (Equiv.sumArrowEquivProdArrow K L ℕ).symm
  have he (x : (K → ℕ) × (L → ℕ)) :
      (independent (Sum.elim μ ν)).weight (e x) * f (fun k => e x (Sum.inl k)) =
        ((independent μ).weight x.1 * f x.1) * (independent ν).weight x.2 := by
    simp only [independent_weight, Fintype.prod_sum_type, e, Equiv.sumArrowEquivProdArrow,
      Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr]
    ring
  have hs := (independent (Sum.elim μ ν)).summable_expect_of_bounded
    (fun x => f (fun k => x (Sum.inl k))) B (fun x => hf _)
  have hp : Summable (fun x : (K → ℕ) × (L → ℕ) =>
      ((independent μ).weight x.1 * f x.1) * (independent ν).weight x.2) :=
    (hs.comp_injective e.injective).congr he
  have ht := ((independent μ).summable_expect_of_bounded f B hf).tsum_mul_tsum
    (independent ν).summable_weight hp
  rw [DiscreteLaw.tsum_weight, mul_one] at ht
  unfold expect
  rw [← e.tsum_eq]
  exact (tsum_congr he).trans ht.symm

theorem expect_independent_subtype (μ : K → DiscreteLaw ℕ) (p : K → Prop) [DecidablePred p]
    (f : ({k // p k} → ℕ) → ℝ) (B : ℝ) (hf : ∀ x, |f x| ≤ B) :
    (independent μ).expect (fun x => f (fun k => x k.val)) =
      (independent (fun k : {k // p k} => μ k.val)).expect f := by
  rw [expect_independent_equiv (Equiv.sumCompl p) μ (fun x => f (fun k => x k.val))]
  have he : (fun k => μ ((Equiv.sumCompl p) k)) =
      Sum.elim (fun k : {k // p k} => μ k.val) (fun k : {k // ¬p k} => μ k.val) := by
    funext k
    cases k <;> rfl
  rw [he]
  simp only [Equiv.sumCompl_apply_symm_of_pos, Subtype.property]
  exact expect_independent_sum_left _ _ f B hf

theorem expect_independent_finset_subset {A : Type*} [DecidableEq A]
    (S T : Finset A) (hTS : T ⊆ S) (μ : S → DiscreteLaw ℕ)
    (f : (T → ℕ) → ℝ) (B : ℝ) (hf : ∀ labels, |f labels| ≤ B) :
    (independent μ).expect (fun labels => f (fun k : T => labels ⟨k.val, hTS k.property⟩)) =
      (independent (fun k : T => μ ⟨k.val, hTS k.property⟩)).expect f := by
  let e : T ≃ {k : S // k.val ∈ T} :=
    { toFun := fun k => ⟨⟨k.val, hTS k.property⟩, k.property⟩
      invFun := fun k => ⟨k.val.val, k.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let g := fun labels : {k : S // k.val ∈ T} → ℕ => f (fun k => labels (e k))
  have hs := expect_independent_subtype μ (fun k : S => k.val ∈ T) g B (fun labels => hf _)
  have he := expect_independent_equiv e (fun k : {k : S // k.val ∈ T} => μ k.val) g
  exact hs.trans (by simpa only [g, Equiv.symm_apply_apply] using he)

end CausalLowerbound.DiscreteLaw

namespace CausalLowerbound.PartC
open PartB
variable {K J Ω : Type*} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype Ω]

theorem sharedSignPrior_expect_finset_subset {A : Type*} [DecidableEq A]
    (S T : Finset A) (hTS : T ⊆ S) (H : S → DiscreteLaw ℕ)
    (f : (J → Bool) → (T → ℕ) → ℝ) (B : ℝ) (hf : ∀ ζ labels, |f ζ labels| ≤ B) :
    (sharedSignPrior H).expect (fun z => f z.2 (fun k : T => z.1 ⟨k.val, hTS k.property⟩)) =
      (sharedSignPrior (fun k : T => H ⟨k.val, hTS k.property⟩)).expect (fun z => f z.2 z.1) := by
  rw [sharedSignPrior_expect H _ B (fun z => hf z.2 _),
    sharedSignPrior_expect (fun k : T => H ⟨k.val, hTS k.property⟩) _ B (fun z => hf z.2 z.1)]
  exact DiscreteLaw.expect_independent_finset_subset S T hTS H
    (fun labels => independentSigns.expect (fun ζ => f ζ labels)) B
    (fun labels => FiniteLaw.abs_expect_le_bound _ _ B (fun ζ => hf ζ labels))

theorem signBlockPrior_expect_subtype (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (p : K → Prop) [DecidablePred p]
    (f : (J → Bool) → ({k // p k} → ℕ) → ({k // p k} → Ω) → ℝ)
    (B : ℝ) (hf : ∀ ζ labels ξ, |f ζ labels ξ| ≤ B) :
    (signBlockPrior H kernel).expect (fun z => f z.1.2 (fun k => z.1.1 k.val) (fun k => z.2 k.val)) =
      (signBlockPrior (fun k : {k // p k} => H k.val) (fun k => kernel k.val)).expect
        (fun z => f z.1.2 z.1.1 z.2) := by
  rw [signBlockPrior_expect_by_sign H kernel
      (fun ζ labels ξ => f ζ (fun k => labels k.val) (fun k => ξ k.val))
      B (fun ζ labels ξ => hf ζ _ _),
    signBlockPrior_expect_by_sign _ _ f B hf]
  apply FiniteLaw.expect_congr
  intro ζ
  have he (labels : K → ℕ) := FiniteLaw.expect_independent_subtype
    (fun k => kernel k ζ (labels k)) p (f ζ (fun k => labels k.val))
  simp_rw [he]
  exact DiscreteLaw.expect_independent_subtype H p
    (fun labels => (FiniteLaw.independent (fun k : {k // p k} => kernel k.val ζ (labels k))).expect (f ζ labels))
    B (fun labels => FiniteLaw.abs_expect_le_bound _ _ B (hf ζ labels))

theorem signBlockPrior_expect_equiv {L : Type*} [Fintype L] [DecidableEq L]
    (e : L ≃ K) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (f : (J → Bool) → (K → ℕ) → (K → Ω) → ℝ)
    (B : ℝ) (hf : ∀ ζ labels ξ, |f ζ labels ξ| ≤ B) :
    (signBlockPrior H kernel).expect (fun z => f z.1.2 z.1.1 z.2) =
      (signBlockPrior (fun k => H (e k)) (fun k => kernel (e k))).expect
        (fun z => f z.1.2 (fun k => z.1.1 (e.symm k)) (fun k => z.2 (e.symm k))) := by
  rw [signBlockPrior_expect_by_sign H kernel f B hf,
    signBlockPrior_expect_by_sign (fun k => H (e k)) (fun k => kernel (e k))
      (fun ζ labels ξ => f ζ (fun k => labels (e.symm k)) (fun k => ξ (e.symm k)))
      B (fun ζ labels ξ => hf ζ _ _)]
  apply FiniteLaw.expect_congr
  intro ζ
  rw [DiscreteLaw.expect_independent_equiv e H]
  congr 1
  funext labels
  rw [FiniteLaw.expect_independent_equiv e]
  simp only [Equiv.symm_apply_apply]

theorem signBlockPrior_expect_finset_subset {A : Type*} [DecidableEq A]
    (S T : Finset A) (hTS : T ⊆ S) (H : S → DiscreteLaw ℕ)
    (kernel : S → (J → Bool) → ℕ → FiniteLaw Ω)
    (f : (J → Bool) → (T → ℕ) → (T → Ω) → ℝ)
    (B : ℝ) (hf : ∀ ζ labels ξ, |f ζ labels ξ| ≤ B) :
    (signBlockPrior H kernel).expect (fun z => f z.1.2
      (fun k : T => z.1.1 ⟨k.val, hTS k.property⟩)
      (fun k : T => z.2 ⟨k.val, hTS k.property⟩)) =
      (signBlockPrior (fun k : T => H ⟨k.val, hTS k.property⟩)
        (fun k : T => kernel ⟨k.val, hTS k.property⟩)).expect
          (fun z => f z.1.2 z.1.1 z.2) := by
  let e : T ≃ {k : S // k.val ∈ T} :=
    { toFun := fun k => ⟨⟨k.val, hTS k.property⟩, k.property⟩
      invFun := fun k => ⟨k.val.val, k.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let g := fun ζ (labels : {k : S // k.val ∈ T} → ℕ)
    (ξ : {k : S // k.val ∈ T} → Ω) => f ζ (fun k => labels (e k)) (fun k => ξ (e k))
  have hg : ∀ ζ labels ξ, |g ζ labels ξ| ≤ B := fun ζ labels ξ => hf ζ _ _
  have hs := signBlockPrior_expect_subtype H kernel (fun k : S => k.val ∈ T) g B hg
  have he := signBlockPrior_expect_equiv e (fun k : {k : S // k.val ∈ T} => H k.val)
    (fun k => kernel k.val) g B hg
  exact hs.trans (by simpa only [g, Equiv.symm_apply_apply] using he)

end CausalLowerbound.PartC

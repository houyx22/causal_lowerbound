import CausalLowerbound.PartC.SharedBlockFactorization
import CausalLowerbound.PartC.SharedSignIncidence

/-! Factor the complete raw observation integrand using the enlarged
incidence graph. Unobserved blocks integrate to one and impose no false
independence condition on their unused coefficient kernels. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB
attribute [local instance] incidenceComponentFintype
variable {V K J Ω : Type*} [Fintype V] [Fintype K] [DecidableEq K]
  [Fintype J] [DecidableEq J] [Fintype Ω] [Inhabited Ω]

def componentBlockOwner (inc : V → K ⊕ J → Prop) (k : K) :
    Option (incidenceGraph inc).ConnectedComponent := blockComponent inc (Sum.inl k)

def extendFiberAssignment {C A : Type*} [Inhabited A] (owner : K → C) (c : C)
    (u : {k // owner k = c} → A) (k : K) : A :=
  if hk : owner k = c then u ⟨k, hk⟩ else default

def SharedObservationLocal (inc : V → K ⊕ J → Prop)
    (f : V → (J → Bool) → (K → ℕ) → (K → Ω) → ℝ) : Prop :=
  ∀ i ζ ζ' labels labels' u u',
    (∀ j, inc i (Sum.inr j) → ζ j = ζ' j) →
    (∀ k, inc i (Sum.inl k) → labels k = labels' k) →
    (∀ k, inc i (Sum.inl k) → u k = u' k) →
    f i ζ labels u = f i ζ' labels' u'

def sharedComponentIntegrand (inc : V → K ⊕ J → Prop)
    (f : V → (J → Bool) → (K → ℕ) → (K → Ω) → ℝ)
    (c : Option (incidenceGraph inc).ConnectedComponent) (ζ : J → Bool)
    (labels : {k // componentBlockOwner inc k = c} → ℕ)
    (u : {k // componentBlockOwner inc k = c} → Ω) : ℝ :=
  ∏ i : {i // siteComponent inc i = c}, f i.val ζ
    (extendFiberAssignment (componentBlockOwner inc) c labels)
    (extendFiberAssignment (componentBlockOwner inc) c u)

theorem sharedComponentIntegrand_restrict (inc : V → K ⊕ J → Prop)
    (f : V → (J → Bool) → (K → ℕ) → (K → Ω) → ℝ) (hf : SharedObservationLocal inc f)
    (c : Option (incidenceGraph inc).ConnectedComponent) (ζ : J → Bool)
    (labels : K → ℕ) (u : K → Ω) :
    sharedComponentIntegrand inc f c ζ (fun k => labels k.val) (fun k => u k.val) =
      ∏ i : {i // siteComponent inc i = c}, f i.val ζ labels u := by
  apply Finset.prod_congr rfl
  intro i _
  apply hf i.val ζ ζ _ labels _ u (fun _ _ => rfl)
  · intro k hk
    have he : componentBlockOwner inc k = c := (blockComponent_of_inc inc i.val (Sum.inl k) hk).trans i.property
    simp only [extendFiberAssignment, dif_pos he]
  · intro k hk
    have he : componentBlockOwner inc k = c := (blockComponent_of_inc inc i.val (Sum.inl k) hk).trans i.property
    simp only [extendFiberAssignment, dif_pos he]

theorem sharedComponentIntegrand_none (inc : V → K ⊕ J → Prop)
    (f : V → (J → Bool) → (K → ℕ) → (K → Ω) → ℝ) (ζ : J → Bool)
    (labels : {k // componentBlockOwner inc k = none} → ℕ)
    (u : {k // componentBlockOwner inc k = none} → Ω) :
    sharedComponentIntegrand inc f none ζ labels u = 1 := by
  apply Finset.prod_eq_one
  intro i _
  exact (by simpa only [siteComponent, reduceCtorEq] using i.property : False).elim

theorem sharedComponentIntegrand_bound (inc : V → K ⊕ J → Prop)
    (f : V → (J → Bool) → (K → ℕ) → (K → Ω) → ℝ) (M : ℝ)
    (hb : ∀ i ζ labels u, |f i ζ labels u| ≤ M)
    (c : Option (incidenceGraph inc).ConnectedComponent) (ζ : J → Bool)
    (labels : {k // componentBlockOwner inc k = c} → ℕ)
    (u : {k // componentBlockOwner inc k = c} → Ω) :
    |sharedComponentIntegrand inc f c ζ labels u| ≤ M ^ Fintype.card {i // siteComponent inc i = c} := by
  unfold sharedComponentIntegrand
  rw [Finset.abs_prod]
  simpa only [Finset.prod_const, Finset.card_univ] using
    Finset.prod_le_prod (s := (Finset.univ : Finset {i // siteComponent inc i = c})) (fun _ _ => abs_nonneg _)
      (fun i _ => hb i.val ζ (extendFiberAssignment (componentBlockOwner inc) c labels)
        (extendFiberAssignment (componentBlockOwner inc) c u))

set_option maxHeartbeats 800000 in
theorem shared_observation_factorization (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (blockInc : V → K → Prop) (siteSigns : V → Finset J) (blockSigns : K → Finset J)
    (hkernel : ∀ k ζ ζ' n, (∀ j ∈ blockSigns k, ζ j = ζ' j) → kernel k ζ n = kernel k ζ' n)
    (f : V → (J → Bool) → (K → ℕ) → (K → Ω) → ℝ)
    (hf : SharedObservationLocal (sharedSignIncidence blockInc siteSigns blockSigns) f)
    (M : ℝ) (hb : ∀ i ζ labels u, |f i ζ labels u| ≤ M) :
    let inc := sharedSignIncidence blockInc siteSigns blockSigns
    (signBlockPrior H kernel).expect (fun z => ∏ i, f i z.1.2 z.1.1 z.2) =
      ∏ c : Option (incidenceGraph inc).ConnectedComponent,
        independentSigns.expect (fun ζ =>
          (DiscreteLaw.independent (fun k : {k // componentBlockOwner inc k = c} => H k.val)).expect
            (signComponentValue (componentBlockOwner inc) kernel (sharedComponentIntegrand inc f) c ζ)) := by
  let inc := sharedSignIncidence blockInc siteSigns blockSigns
  let owner := componentBlockOwner inc
  let F := sharedComponentIntegrand inc f
  have he (ζ : J → Bool) (labels : K → ℕ) (u : K → Ω) :
      (∏ i, f i ζ labels u) = ∏ c : Option (incidenceGraph inc).ConnectedComponent,
        F c ζ (fun k => labels k.val) (fun k => u k.val) := by
    simp only [F, sharedComponentIntegrand_restrict inc f hf]
    exact (Fintype.prod_fiberwise (siteComponent inc) (fun i => f i ζ labels u)).symm
  dsimp only
  simp_rw [he]
  apply signBlockPrior_component_factorization H kernel owner (componentSignSet inc)
    (componentSignSet_disjoint inc) F
    (fun c => M ^ Fintype.card {i // siteComponent inc i = c})
    (sharedComponentIntegrand_bound inc f M hb)
  intro c ζ ζ' labels hζ
  cases c with
  | none =>
    rw [signComponentValue_eq_one owner kernel F none ζ labels
      (sharedComponentIntegrand_none inc f ζ labels),
      signComponentValue_eq_one owner kernel F none ζ' labels
      (sharedComponentIntegrand_none inc f ζ' labels)]
  | some c =>
    apply signComponentValue_local_congr owner kernel F (some c) ζ ζ' labels
    · intro k
      apply hkernel k.val ζ ζ' (labels k)
      intro j hj
      exact hζ j (blockSigns_subset_component blockInc siteSigns blockSigns k.val (some c)
        k.property (by simp) hj)
    · intro u
      apply Finset.prod_congr rfl
      intro i _
      apply hf i.val ζ ζ' _ _ _ _
      · intro j hij
        exact hζ j ((mem_componentSignSet inc (some c) j).mpr ⟨i.val, i.property, hij⟩)
      · exact fun _ _ => rfl
      · exact fun _ _ => rfl

end CausalLowerbound.PartC

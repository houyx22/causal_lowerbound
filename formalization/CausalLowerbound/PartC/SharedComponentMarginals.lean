import CausalLowerbound.PartC.BlockPriorRestriction
import CausalLowerbound.PartC.SharedObservationFactorization

/-! Identify the component factors with expectations under the original
shared-sign prior. Each component keeps exactly its own observations;
unused block variables are marginalized, without changing the prior. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB
attribute [local instance] incidenceComponentFintype
variable {V K J Ω : Type*} [Fintype V] [Fintype K] [DecidableEq K]
  [Fintype J] [DecidableEq J] [Fintype Ω] [Inhabited Ω]

theorem sharedComponentValue_eq_marginal (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (inc : V → K ⊕ J → Prop)
    (f : V → (J → Bool) → (K → ℕ) → (K → Ω) → ℝ)
    (hf : SharedObservationLocal inc f) (M : ℝ)
    (hb : ∀ i ζ labels u, |f i ζ labels u| ≤ M)
    (c : Option (incidenceGraph inc).ConnectedComponent) :
    independentSigns.expect (fun ζ =>
      (DiscreteLaw.independent (fun k : {k // componentBlockOwner inc k = c} => H k.val)).expect
        (signComponentValue (componentBlockOwner inc) kernel (sharedComponentIntegrand inc f) c ζ)) =
      (signBlockPrior H kernel).expect (fun z =>
        ∏ i : {i // siteComponent inc i = c}, f i.val z.1.2 z.1.1 z.2) := by
  let g := sharedComponentIntegrand inc f c
  let B := M ^ Fintype.card {i // siteComponent inc i = c}
  have hg : ∀ ζ labels u, |g ζ labels u| ≤ B := sharedComponentIntegrand_bound inc f M hb c
  have hs := signBlockPrior_expect_subtype H kernel (fun k => componentBlockOwner inc k = c) g B hg
  have he := signBlockPrior_expect_by_sign
    (fun k : {k // componentBlockOwner inc k = c} => H k.val) (fun k => kernel k.val) g B hg
  simpa only [g, signComponentValue, sharedComponentIntegrand_restrict inc f hf c] using (hs.trans he).symm

theorem shared_observation_factorization_marginals (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (blockInc : V → K → Prop) (siteSigns : V → Finset J) (blockSigns : K → Finset J)
    (hkernel : ∀ k ζ ζ' n, (∀ j ∈ blockSigns k, ζ j = ζ' j) → kernel k ζ n = kernel k ζ' n)
    (f : V → (J → Bool) → (K → ℕ) → (K → Ω) → ℝ)
    (hf : SharedObservationLocal (sharedSignIncidence blockInc siteSigns blockSigns) f)
    (M : ℝ) (hb : ∀ i ζ labels u, |f i ζ labels u| ≤ M) :
    let inc := sharedSignIncidence blockInc siteSigns blockSigns
    (signBlockPrior H kernel).expect (fun z => ∏ i, f i z.1.2 z.1.1 z.2) =
      ∏ c : Option (incidenceGraph inc).ConnectedComponent,
        (signBlockPrior H kernel).expect (fun z =>
          ∏ i : {i // siteComponent inc i = c}, f i.val z.1.2 z.1.1 z.2) := by
  dsimp only
  rw [shared_observation_factorization H kernel blockInc siteSigns blockSigns hkernel f hf M hb]
  apply Finset.prod_congr rfl
  intro c _
  exact sharedComponentValue_eq_marginal H kernel _ f hf M hb c

end CausalLowerbound.PartC

import CausalLowerbound.PartB.ComponentHellinger
import CausalLowerbound.FiniteReindex

/-! Restricting an actual component law preserves precisely the block
laws that can affect it; all other block coordinates integrate out. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators Classical
namespace CausalLowerbound
namespace FiniteLaw
variable {K Ω Λ : Type*} [Fintype K] [DecidableEq K] [Fintype Ω] [Inhabited Ω] [Fintype Λ]

theorem expect_independent_local (μ ν : K → FiniteLaw Ω) (p : K → Prop)
    (hμ : ∀ k, p k → μ k = ν k) (f : (K → Ω) → ℝ)
    (hf : ∀ x y, (∀ k, p k → x k = y k) → f x = f y) :
    (independent μ).expect f = (independent ν).expect f := by
  let g : ({k // p k} → Ω) → ℝ := fun u => f (fun k => if hk : p k then u ⟨k, hk⟩ else default)
  have he (x : K → Ω) : f x = g (fun k => x k.val) := by
    apply hf
    intro k hk
    simp [hk]
  have hh : (fun k : {k // p k} => μ k.val) = (fun k : {k // p k} => ν k.val) :=
    funext (fun k => hμ k.val k.property)
  calc
    _ = (independent μ).expect (fun x => g (fun k => x k.val)) := expect_congr _ he
    _ = (independent (fun k : {k // p k} => μ k.val)).expect g := expect_independent_subtype μ p g
    _ = (independent (fun k : {k // p k} => ν k.val)).expect g := by rw [hh]
    _ = (independent ν).expect (fun x => g (fun k => x k.val)) := (expect_independent_subtype ν p g).symm
    _ = (independent ν).expect f := expect_congr _ (fun x => (he x).symm)

omit [Inhabited Ω] in
theorem hellingerSq_eq_of_weight_equiv (e : Ω ≃ Λ) (P Q : FiniteLaw Ω) (R S : FiniteLaw Λ)
    (hP : ∀ x, P.weight x = R.weight (e x)) (hQ : ∀ x, Q.weight x = S.weight (e x)) :
    P.hellingerSq Q = R.hellingerSq S := by
  unfold hellingerSq
  simp_rw [hP, hQ]
  exact e.sum_comp (fun x => (Real.sqrt (R.weight x) - Real.sqrt (S.weight x)) ^ 2)

end FiniteLaw
namespace PartB
attribute [local instance] incidenceComponentFintype
variable {V K Ω Y : Type*} [Fintype V] [Fintype K] [DecidableEq K]
  [Fintype Ω] [Inhabited Ω] [Fintype Y]

theorem componentOutputLaw_weight_full (μ : K → FiniteLaw Ω) (inc : V → K → Prop)
    (L : V → (K → Ω) → FiniteLaw Y)
    (hL : ∀ i x y, (∀ k, inc i k → x k = y k) → L i x = L i y)
    (c : Option (incidenceGraph inc).ConnectedComponent)
    (w : {i // siteComponent inc i = c} → Y) :
    (componentOutputLaw μ inc L c).weight w =
      (FiniteLaw.independent μ).expect
        (fun z => ∏ i : {i // siteComponent inc i = c}, (L i.val z).weight (w i)) := by
  have hf (z : K → Ω) :
      (∏ i : {i // siteComponent inc i = c}, (L i.val z).weight (w i)) =
        ∏ i : {i // siteComponent inc i = c},
          (L i.val (extendComponentCoefficients inc c (fun k => z k.val))).weight (w i) := by
    apply Finset.prod_congr rfl
    intro i _
    congr 1
    apply hL
    intro k hk
    have he := (blockComponent_of_inc inc i.val k hk).trans i.property
    simp [extendComponentCoefficients, he]
  calc
    _ = (FiniteLaw.independent (fun k : {k // blockComponent inc k = c} => μ k.val)).expect
        (fun z => ∏ i : {i // siteComponent inc i = c},
          (L i.val (extendComponentCoefficients inc c z)).weight (w i)) := rfl
    _ = (FiniteLaw.independent μ).expect (fun z =>
        ∏ i : {i // siteComponent inc i = c},
          (L i.val (extendComponentCoefficients inc c (fun k => z k.val))).weight (w i)) :=
      by
        have he := FiniteLaw.expect_independent_subtype μ (fun k => blockComponent inc k = c)
          (fun z => ∏ i : {i // siteComponent inc i = c},
            (L i.val (extendComponentCoefficients inc c z)).weight (w i))
        exact he.symm
    _ = _ := FiniteLaw.expect_congr _ (fun z => (hf z).symm)

theorem componentOutputLaw_congr_blocks (μ ν : K → FiniteLaw Ω) (inc : V → K → Prop)
    (L : V → (K → Ω) → FiniteLaw Y)
    (hL : ∀ i x y, (∀ k, inc i k → x k = y k) → L i x = L i y)
    (c : Option (incidenceGraph inc).ConnectedComponent)
    (hμ : ∀ k, blockComponent inc k = c → μ k = ν k) :
    componentOutputLaw μ inc L c = componentOutputLaw ν inc L c := by
  apply FiniteLaw.ext
  intro w
  rw [componentOutputLaw_weight_full μ inc L hL, componentOutputLaw_weight_full ν inc L hL]
  apply FiniteLaw.expect_independent_local μ ν (fun k => blockComponent inc k = c) hμ
  intro x y hxy
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  exact hL i.val x y (fun k hk => hxy k ((blockComponent_of_inc inc i.val k hk).trans i.property))

end PartB
end CausalLowerbound

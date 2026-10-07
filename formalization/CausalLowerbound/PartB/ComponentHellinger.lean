import CausalLowerbound.PartB.ComponentFactorization
import CausalLowerbound.FiniteTesting

/-! Hellinger tensorization along the actual observation components. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound
namespace FiniteLaw
variable {V C Y : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Fintype Y]

theorem hellingerSq_fiber_factorization (c : V → C) (P Q : FiniteLaw (V → Y))
    (Pc Qc : ∀ a, FiniteLaw ({i // c i = a} → Y))
    (hP : ∀ w, P.weight w = ∏ a, (Pc a).weight (fun i => w i.val))
    (hQ : ∀ w, Q.weight w = ∏ a, (Qc a).weight (fun i => w i.val)) :
    P.hellingerSq Q = (independent Pc).hellingerSq (independent Qc) := by
  unfold hellingerSq
  rw [← (fiberGrouping c).sum_comp]
  apply Finset.sum_congr rfl
  intro w _
  simp only [hP, hQ, independent, fiberGrouping, Equiv.coe_fn_mk]

theorem hellingerSq_fiber_factorization_le (c : V → C) (P Q : FiniteLaw (V → Y))
    (Pc Qc : ∀ a, FiniteLaw ({i // c i = a} → Y))
    (hP : ∀ w, P.weight w = ∏ a, (Pc a).weight (fun i => w i.val))
    (hQ : ∀ w, Q.weight w = ∏ a, (Qc a).weight (fun i => w i.val)) :
    P.hellingerSq Q ≤ ∑ a, (Pc a).hellingerSq (Qc a) := by
  rw [hellingerSq_fiber_factorization c P Q Pc Qc hP hQ]
  exact hellingerSq_independent_le Pc Qc

end FiniteLaw
namespace PartB
attribute [local instance] incidenceComponentFintype
variable {V K Ω Y : Type*} [Fintype V] [Fintype K] [DecidableEq K]
  [Fintype Ω] [Inhabited Ω] [Fintype Y]

theorem mixed_output_component_hellinger (μ ν : K → FiniteLaw Ω) (inc : V → K → Prop)
    (P Q : V → (K → Ω) → FiniteLaw Y)
    (hP : ∀ i x y, (∀ k, inc i k → x k = y k) → P i x = P i y)
    (hQ : ∀ i x y, (∀ k, inc i k → x k = y k) → Q i x = Q i y) :
    ((FiniteLaw.independent μ).mixture (fun x => FiniteLaw.independent (fun i => P i x))).hellingerSq
      ((FiniteLaw.independent ν).mixture (fun x => FiniteLaw.independent (fun i => Q i x))) ≤
        ∑ c : Option (incidenceGraph inc).ConnectedComponent,
          (componentOutputLaw μ inc P c).hellingerSq (componentOutputLaw ν inc Q c) := by
  exact FiniteLaw.hellingerSq_fiber_factorization_le (siteComponent inc) _ _
    (componentOutputLaw μ inc P) (componentOutputLaw ν inc Q)
    (mixed_output_component_factorization μ inc P hP)
    (mixed_output_component_factorization ν inc Q hQ)

end PartB
end CausalLowerbound

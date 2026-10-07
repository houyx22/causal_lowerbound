import CausalLowerbound.FiniteGrouping
import CausalLowerbound.PartB.ObservationGraph

/-! Exact component factorization from the actual incidence graph and
independent finite coefficient laws. Unused blocks form a harmless extra fiber. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.PartB
variable {V K Ω Y : Type*} [Fintype V] [Fintype K] [DecidableEq K]
  [Fintype Ω] [Inhabited Ω] [Fintype Y]
local instance incidenceComponentFintype (inc : V → K → Prop) :
    Fintype (incidenceGraph inc).ConnectedComponent := by
  unfold SimpleGraph.ConnectedComponent
  exact Fintype.ofFinite _

def blockComponent (inc : V → K → Prop) (k : K) : Option (incidenceGraph inc).ConnectedComponent :=
  if h : ∃ i, inc i k then some ((incidenceGraph inc).connectedComponentMk h.choose) else none

def siteComponent (inc : V → K → Prop) (i : V) : Option (incidenceGraph inc).ConnectedComponent :=
  some ((incidenceGraph inc).connectedComponentMk i)

theorem blockComponent_of_inc (inc : V → K → Prop) (i : V) (k : K) (hi : inc i k) :
    blockComponent inc k = siteComponent inc i := by
  have he : ∃ i, inc i k := ⟨i, hi⟩
  rw [blockComponent, dif_pos he]
  exact congrArg some (common_label_same_component inc he.choose i k he.choose_spec hi)

def extendComponentCoefficients (inc : V → K → Prop)
    (c : Option (incidenceGraph inc).ConnectedComponent)
    (u : {k // blockComponent inc k = c} → Ω) : K → Ω :=
  fun k => if hk : blockComponent inc k = c then u ⟨k, hk⟩ else default

def componentIntegrand (inc : V → K → Prop) (f : V → (K → Ω) → ℝ)
    (c : Option (incidenceGraph inc).ConnectedComponent)
    (u : {k // blockComponent inc k = c} → Ω) : ℝ :=
  ∏ i : {i // siteComponent inc i = c}, f i.val (extendComponentCoefficients inc c u)

theorem componentIntegrand_restrict (inc : V → K → Prop) (f : V → (K → Ω) → ℝ)
    (hlocal : ∀ i x y, (∀ k, inc i k → x k = y k) → f i x = f i y)
    (c : Option (incidenceGraph inc).ConnectedComponent) (x : K → Ω) :
    componentIntegrand inc f c (fun k => x k.val) = ∏ i : {i // siteComponent inc i = c}, f i.val x := by
  apply Finset.prod_congr rfl
  intro i _
  apply hlocal
  intro k hk
  have he := (blockComponent_of_inc inc i.val k hk).trans i.property
  simp [extendComponentCoefficients, he]

theorem independent_incidence_factorization (μ : K → FiniteLaw Ω) (inc : V → K → Prop)
    (f : V → (K → Ω) → ℝ)
    (hlocal : ∀ i x y, (∀ k, inc i k → x k = y k) → f i x = f i y) :
    (FiniteLaw.independent μ).expect (fun x => ∏ i, f i x) =
      ∏ c : Option (incidenceGraph inc).ConnectedComponent,
        (FiniteLaw.independent (fun k : {k // blockComponent inc k = c} => μ k.val)).expect
          (componentIntegrand inc f c) := by
  have he (x : K → Ω) : (∏ i, f i x) =
      ∏ c : Option (incidenceGraph inc).ConnectedComponent,
        componentIntegrand inc f c (fun k => x k.val) := by
    simp_rw [componentIntegrand_restrict inc f hlocal]
    exact (Fintype.prod_fiberwise (siteComponent inc) (fun i => f i x)).symm
  simp_rw [he]
  exact FiniteLaw.expect_independent_component_prod μ (blockComponent inc) (componentIntegrand inc f)

def componentOutputLaw (μ : K → FiniteLaw Ω) (inc : V → K → Prop)
    (L : V → (K → Ω) → FiniteLaw Y) (c : Option (incidenceGraph inc).ConnectedComponent) :
    FiniteLaw ({i // siteComponent inc i = c} → Y) :=
  (FiniteLaw.independent (fun k : {k // blockComponent inc k = c} => μ k.val)).mixture
    (fun u => FiniteLaw.independent (fun i : {i // siteComponent inc i = c} =>
      L i.val (extendComponentCoefficients inc c u)))

theorem mixed_output_component_factorization (μ : K → FiniteLaw Ω) (inc : V → K → Prop)
    (L : V → (K → Ω) → FiniteLaw Y)
    (hlocal : ∀ i x y, (∀ k, inc i k → x k = y k) → L i x = L i y) (w : V → Y) :
    ((FiniteLaw.independent μ).mixture (fun x => FiniteLaw.independent (fun i => L i x))).weight w =
      ∏ c : Option (incidenceGraph inc).ConnectedComponent,
        (componentOutputLaw μ inc L c).weight (fun i => w i.val) := by
  exact independent_incidence_factorization μ inc (fun i x => (L i x).weight (w i))
    (fun i x y h => congrArg (fun law : FiniteLaw Y => law.weight (w i)) (hlocal i x y h))

end CausalLowerbound.PartB

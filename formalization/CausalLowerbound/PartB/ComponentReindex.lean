import CausalLowerbound.PartB.ComponentRestriction
import CausalLowerbound.PartB.PhysicalActivation

/-! Reindex actual components by finite intervals while preserving the
factorization and Hellinger bound, including the empty unused-block fiber. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators Classical
namespace CausalLowerbound
namespace FiniteLaw
attribute [local instance] PartB.ShellGeometry.finOrderedDecEq PartB.ShellGeometry.finOrderedDecLt
variable {V K C Ω Y : Type*} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
  [Fintype C] [DecidableEq C] [Fintype Ω] [Fintype Y]

def reindexedFiberGrouping (c : V → C) (m : C → ℕ)
    (e : ∀ a, Fin (m a) ≃ {i // c i = a}) : (V → Y) ≃ (∀ a, Fin (m a) → Y) :=
  (fiberGrouping c).trans (Equiv.piCongrRight (fun a =>
    Equiv.arrowCongr (e a).symm (Equiv.refl Y)))

def restrictedExperiment (μ : K → FiniteLaw Ω) (L : V → (K → Ω) → FiniteLaw Y)
    {m : ℕ} (v : Fin m → V) : FiniteLaw (Fin m → Y) :=
  (independent μ).mixture (fun z => independent (fun i => L (v i) z))

theorem restrictedExperiment_weight (μ : K → FiniteLaw Ω) (L : V → (K → Ω) → FiniteLaw Y)
    {m : ℕ} (v : Fin m → V) (w : Fin m → Y) :
    (restrictedExperiment μ L v).weight w = (independent μ).expect (fun z => ∏ i, (L (v i) z).weight (w i)) := rfl

end FiniteLaw
namespace PartB
attribute [local instance] ShellGeometry.finOrderedDecEq ShellGeometry.finOrderedDecLt incidenceComponentFintype
variable {V K Ω Y : Type*} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
  [Fintype Ω] [Inhabited Ω] [Fintype Y]

theorem reindexed_component_factorization (μ : K → FiniteLaw Ω) (inc : V → K → Prop)
    (L : V → (K → Ω) → FiniteLaw Y)
    (hL : ∀ i x y, (∀ k, inc i k → x k = y k) → L i x = L i y)
    (m : Option (incidenceGraph inc).ConnectedComponent → ℕ)
    (e : ∀ c, Fin (m c) ≃ {i // siteComponent inc i = c}) (w : V → Y) :
    ((FiniteLaw.independent μ).mixture (fun z => FiniteLaw.independent (fun i => L i z))).weight w =
      ∏ c, (FiniteLaw.restrictedExperiment μ L (fun j => (e c j).val)).weight (fun j => w (e c j).val) := by
  change (FiniteLaw.independent μ).expect (fun z => ∏ i, (L i z).weight (w i)) = _
  let f : V → (K → Ω) → ℝ := fun i z => (L i z).weight (w i)
  have hf : ∀ i x y, (∀ k, inc i k → x k = y k) → f i x = f i y :=
    fun i x y h => congrArg (fun law => law.weight (w i)) (hL i x y h)
  rw [independent_incidence_factorization μ inc f hf]
  apply Finset.prod_congr rfl
  intro c _
  have hh := FiniteLaw.expect_independent_subtype μ (fun k => blockComponent inc k = c)
    (componentIntegrand inc f c)
  rw [← hh, FiniteLaw.restrictedExperiment_weight]
  apply FiniteLaw.expect_congr
  intro z
  rw [componentIntegrand_restrict inc f hf c z]
  exact ((e c).prod_comp (fun i => f i.val z)).symm

theorem reindexed_component_hellinger (μ ν : K → FiniteLaw Ω) (inc : V → K → Prop)
    (P Q : V → (K → Ω) → FiniteLaw Y)
    (hP : ∀ i x y, (∀ k, inc i k → x k = y k) → P i x = P i y)
    (hQ : ∀ i x y, (∀ k, inc i k → x k = y k) → Q i x = Q i y)
    (m : Option (incidenceGraph inc).ConnectedComponent → ℕ)
    (e : ∀ c, Fin (m c) ≃ {i // siteComponent inc i = c}) :
    ((FiniteLaw.independent μ).mixture (fun z => FiniteLaw.independent (fun i => P i z))).hellingerSq
      ((FiniteLaw.independent ν).mixture (fun z => FiniteLaw.independent (fun i => Q i z))) ≤
        ∑ c, (FiniteLaw.restrictedExperiment μ P (fun j => (e c j).val)).hellingerSq
          (FiniteLaw.restrictedExperiment ν Q (fun j => (e c j).val)) := by
  let Pc := fun c => FiniteLaw.restrictedExperiment μ P (fun j => (e c j).val)
  let Qc := fun c => FiniteLaw.restrictedExperiment ν Q (fun j => (e c j).val)
  have he := FiniteLaw.hellingerSq_eq_of_weight_equiv (FiniteLaw.reindexedFiberGrouping (siteComponent inc) m e)
    ((FiniteLaw.independent μ).mixture (fun z => FiniteLaw.independent (fun i => P i z)))
    ((FiniteLaw.independent ν).mixture (fun z => FiniteLaw.independent (fun i => Q i z)))
    (FiniteLaw.independent Pc) (FiniteLaw.independent Qc)
    (reindexed_component_factorization μ inc P hP m e)
    (reindexed_component_factorization ν inc Q hQ m e)
  rw [he]
  exact FiniteLaw.hellingerSq_independent_le Pc Qc

end PartB
end CausalLowerbound

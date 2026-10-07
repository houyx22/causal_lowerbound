import CausalLowerbound.PartB.GhostReindex
import CausalLowerbound.PartB.PhysicalActivation
import CausalLowerbound.PartB.GlobalGhostCost

/-! Restrict a physical observation configuration to a connected component.
The incident coefficient posterior and averaged taper remain exactly the
same after reindexing the retained observations and ghost coordinates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt incidenceComponentFintype physicalComponentFintype
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

def componentConfiguration (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) {n m : ℕ}
    (x : Fin n → d → ℝ) (c : Option (observationGraph S x₀ r x).ConnectedComponent)
    (e : Fin m ≃ {i // siteComponent (fun j (k : S) => x j ∈ carrierBox x₀ r k.val) i = c}) :
    Fin m → d → ℝ := fun i => x (e i).val

def componentCarrierSitesEquiv (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) {n m : ℕ}
    (x : Fin n → d → ℝ) (c : Option (observationGraph S x₀ r x).ConnectedComponent)
    (e : Fin m ≃ {i // siteComponent (fun j (k : S) => x j ∈ carrierBox x₀ r k.val) i = c})
    (k : S) (hk : blockComponent (fun j (b : S) => x j ∈ carrierBox x₀ r b.val) k = c) :
    carrierSites x₀ r k.val (componentConfiguration S x₀ r x c e) ≃ carrierSites x₀ r k.val x where
  toFun i := ⟨(e i.val).val, by
    simpa only [carrierSites, Finset.mem_filter, Finset.mem_univ, true_and, componentConfiguration] using i.property⟩
  invFun i := ⟨e.symm ⟨i.val, (blockComponent_of_inc
      (fun j (b : S) => x j ∈ carrierBox x₀ r b.val) i.val k (Finset.mem_filter.mp i.property).2).symm.trans hk⟩, by
    simp only [carrierSites, Finset.mem_filter, Finset.mem_univ, true_and,
      componentConfiguration, Equiv.apply_symm_apply]
    exact (Finset.mem_filter.mp i.property).2⟩
  left_inv i := by
    apply Subtype.ext
    apply e.injective
    apply Subtype.ext
    simp
  right_inv i := by
    apply Subtype.ext
    simp

theorem componentCarrierSites_empty_of_ne (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) {n m : ℕ}
    (x : Fin n → d → ℝ) (c : Option (observationGraph S x₀ r x).ConnectedComponent)
    (e : Fin m ≃ {i // siteComponent (fun j (k : S) => x j ∈ carrierBox x₀ r k.val) i = c})
    (k : S) (hk : blockComponent (fun j (b : S) => x j ∈ carrierBox x₀ r b.val) k ≠ c) :
    carrierSites x₀ r k.val (componentConfiguration S x₀ r x c e) = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro i hi
  apply hk
  exact (blockComponent_of_inc (fun j (b : S) => x j ∈ carrierBox x₀ r b.val)
    (e i).val k (Finset.mem_filter.mp hi).2).trans (e i).property

theorem physicalCoefficientPosteriors_component (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x₀ : d → ℝ) (r : ℝ) {n m : ℕ} (x : Fin n → d → ℝ)
    (c : Option (observationGraph S x₀ r x).ConnectedComponent)
    (e : Fin m ≃ {i // siteComponent (fun j (k : S) => x j ∈ carrierBox x₀ r k.val) i = c})
    (k : S) (hk : blockComponent (fun j (b : S) => x j ∈ carrierBox x₀ r b.val) k = c) :
    physicalCoefficientPosteriors H kernel Q S θ hθ hθ1 x₀ r (componentConfiguration S x₀ r x c e) k =
      physicalCoefficientPosteriors H kernel Q S θ hθ hθ1 x₀ r x k := by
  let a := componentCarrierSitesEquiv S x₀ r x c e k hk
  have he := coefficientPosterior_equiv H kernel Q θ hθ hθ1 a
    (fun i : carrierSites x₀ r k.val x =>
      torusProjection (carrierCoordinate (localCoordinate x₀ r k.val (x i.val))))
  exact he

theorem evaluatedBlockWeight_component (H : DiscreteLaw ℕ) (Q : ℕ) (θ ε : ℝ)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) {n m : ℕ} (x : Fin n → d → ℝ)
    (c : Option (observationGraph S x₀ r x).ConnectedComponent)
    (e : Fin m ≃ {i // siteComponent (fun j (k : S) => x j ∈ carrierBox x₀ r k.val) i = c})
    (k : S) (hk : blockComponent (fun j (b : S) => x j ∈ carrierBox x₀ r b.val) k = c)
    (hl : (carrierSites x₀ r k.val (componentConfiguration S x₀ r x c e)).card ≤ Q)
    (hf : (carrierSites x₀ r k.val x).card ≤ Q) :
    evaluatedBlockWeight H Q θ ε (carrierSites x₀ r k.val (componentConfiguration S x₀ r x c e))
      (siteCompletion Q _ hl) (physicalBlockCoordinates x₀ r (componentConfiguration S x₀ r x c e) k.val) =
      evaluatedBlockWeight H Q θ ε (carrierSites x₀ r k.val x)
        (siteCompletion Q _ hf) (physicalBlockCoordinates x₀ r x k.val) := by
  let a := componentCarrierSitesEquiv S x₀ r x c e k hk
  have hc : (carrierSites x₀ r k.val (componentConfiguration S x₀ r x c e)).card =
      (carrierSites x₀ r k.val x).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr a
  let b := finCongr (congrArg (fun j => Q - j) hc)
  have he := ghostActivation_reindex H Q θ ε (siteCompletion Q _ hl) (siteCompletion Q _ hf) a b
    (fun i : carrierSites x₀ r k.val x => torusProjection (physicalBlockCoordinates x₀ r x k.val i.val))
  exact he

end CausalLowerbound.PartB.ShellGeometry

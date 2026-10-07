import CausalLowerbound.PartC.RetainedDesignProduct
import CausalLowerbound.PartC.UnitCubeGhosts

/-! Actual observation slots supplied by the retained/ghost completion.
Only observations incident to a carrier need a distinct slot; all other
observations have zero smooth contribution from that carrier. -/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry ConfigurationShells
variable {d I G : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype G]

theorem linearPartition_nonzero_mem_carrierBox (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ)
    (x : d → ℝ) (hx : linearPartition (localCoordinate x₀ r k x) ≠ 0) :
    x ∈ carrierBox x₀ r k := by
  have hb := linearPartition_support (subset_tsupport _ hx)
  exact ⟨fun a => (by norm_num : (-2 : ℝ) ≤ -1).trans (hb.1 a),
    fun a => (hb.2 a).trans (by norm_num : (1 : ℝ) ≤ 2)⟩

def retainedObservationSlot (Q : ℕ) (hQ : 0 < Q) (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ)
    (x : I → d → ℝ) (e : {i // x i ∈ carrierBox x₀ r k} ⊕ G ≃ Fin Q) (i : I) : Fin Q :=
  if hi : x i ∈ carrierBox x₀ r k then e (Sum.inl ⟨i, hi⟩) else ⟨0, hQ⟩

theorem retainedObservationSlot_incident (Q : ℕ) (hQ : 0 < Q) (x₀ : d → ℝ)
    (r : ℝ) (k : d → ℤ) (x : I → d → ℝ)
    (e : {i // x i ∈ carrierBox x₀ r k} ⊕ G ≃ Fin Q) (i : I)
    (hi : x i ∈ carrierBox x₀ r k) :
    retainedObservationSlot Q hQ x₀ r k x e i = e (Sum.inl ⟨i, hi⟩) := by
  simp only [retainedObservationSlot, dif_pos hi]

theorem retainedObservationSlot_injective_on_incident (Q : ℕ) (hQ : 0 < Q)
    (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) (x : I → d → ℝ)
    (e : {i // x i ∈ carrierBox x₀ r k} ⊕ G ≃ Fin Q) (i j : I)
    (hi : x i ∈ carrierBox x₀ r k) (hj : x j ∈ carrierBox x₀ r k)
    (he : retainedObservationSlot Q hQ x₀ r k x e i = retainedObservationSlot Q hQ x₀ r k x e j) :
    i = j := by
  rw [retainedObservationSlot_incident Q hQ x₀ r k x e i hi,
    retainedObservationSlot_incident Q hQ x₀ r k x e j hj] at he
  exact congrArg Subtype.val (Sum.inl.inj (e.injective he))

theorem retainedObservationSlot_configuration (Q : ℕ) (hQ : 0 < Q) (x₀ : d → ℝ)
    (r : ℝ) (k : d → ℤ) (x : I → d → ℝ)
    (e : {i // x i ∈ carrierBox x₀ r k} ⊕ G ≃ Fin Q) (ghost : G → d → ℝ)
    (i : I) (hi : linearPartition (localCoordinate x₀ r k (x i)) ≠ 0) :
    configurationSite (completedConfiguration e
      (fun j => carrierCoordinate (localCoordinate x₀ r k (x j.val))) ghost)
        (retainedObservationSlot Q hQ x₀ r k x e i) =
      carrierCoordinate (localCoordinate x₀ r k (x i)) := by
  rw [retainedObservationSlot_incident Q hQ x₀ r k x e i
    (linearPartition_nonzero_mem_carrierBox x₀ r k (x i) hi)]
  funext a
  exact congrFun (completedSites_retained e
    (fun j => carrierCoordinate (localCoordinate x₀ r k (x j.val))) ghost
      ⟨i, linearPartition_nonzero_mem_carrierBox x₀ r k (x i) hi⟩) a

end CausalLowerbound.PartC

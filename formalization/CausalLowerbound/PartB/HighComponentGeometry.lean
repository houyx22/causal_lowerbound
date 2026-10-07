import CausalLowerbound.PartB.ObservationGraph
import Mathlib.Data.Finset.Card

/-! A large connected component contains Q+1 distinct observations in a
physical O(Qr) cluster. This uses finite paths, not a supplied forest bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped Classical
namespace CausalLowerbound.PartB
variable {V : Type*} [Fintype V] [DecidableEq V]

def reachableVertices (G : SimpleGraph V) (root : V) : Finset V :=
  Finset.univ.filter (G.Reachable root)

theorem walk_take_length (G : SimpleGraph V) {u v : V} (p : G.Walk u v) (n : ℕ) :
    (p.take n).length = min n p.length := by
  induction p generalizing n with
  | nil => simp [SimpleGraph.Walk.take]
  | cons h p ih =>
    cases n with
    | zero => simp [SimpleGraph.Walk.take]
    | succ n => simp [SimpleGraph.Walk.take, ih, Nat.succ_min_succ]

theorem large_reachable_cluster (G : SimpleGraph V) (root : V) (Q : ℕ)
    (hcard : Q + 1 ≤ (reachableVertices G root).card) :
    ∃ v : Fin (Q + 1) → V, Function.Injective v ∧
      ∀ i, ∃ p : G.Walk root (v i), p.length ≤ Q := by
  by_cases hs : ∀ v, v ∈ reachableVertices G root → ∃ p : G.Walk root v, p.length ≤ Q
  · obtain ⟨s, hsub, hsize⟩ := Finset.exists_subset_card_eq hcard
    let e : Fin (Q + 1) ≃ s := Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_coe, hsize])
    refine ⟨fun i => (e i).val, ?_, fun i => hs (e i).val (hsub (e i).property)⟩
    intro i j hij
    exact e.injective (Subtype.ext hij)
  · push_neg at hs
    obtain ⟨v, hv, hlong⟩ := hs
    obtain ⟨p⟩ := (Finset.mem_filter.mp hv).2
    let p' := p.toPath.val
    have hp : p'.IsPath := p.toPath.property
    have hlen : Q < p'.length := hlong p'
    refine ⟨fun i => p'.getVert i.val, ?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn (by have := i.isLt; change i.val ≤ p'.length; omega)
        (by have := j.isLt; change j.val ≤ p'.length; omega) hij
    · intro i
      refine ⟨p'.take i.val, ?_⟩
      rw [walk_take_length]
      exact (min_le_left _ _).trans (Nat.le_of_lt_succ i.isLt)

namespace ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem observation_large_cluster (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (hr : 0 < r) (x : V → d → ℝ) (root : V) (Q : ℕ)
    (hcard : Q + 1 ≤ (reachableVertices (observationGraph S x₀ r x) root).card) :
    ∃ v : Fin (Q + 1) → V, Function.Injective v ∧
      ∀ i a, |x (v i) a - x root a| ≤ 4 * r * Q := by
  obtain ⟨v, hv, hp⟩ := large_reachable_cluster (observationGraph S x₀ r x) root Q hcard
  refine ⟨v, hv, ?_⟩
  intro i a
  obtain ⟨p, hlen⟩ := hp i
  rw [abs_sub_comm]
  exact (observationGraph_walk_distance S x₀ r hr x p a).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hlen) (by positivity))

theorem large_component_root_incident (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (x : V → d → ℝ) (root : V)
    (hcard : 1 < (reachableVertices (observationGraph S x₀ r x) root).card) :
    ∃ k : S, x root ∈ carrierBox x₀ r k.val := by
  obtain ⟨v, hv, hne⟩ := Finset.exists_mem_ne hcard root
  obtain ⟨p⟩ := (Finset.mem_filter.mp hv).2
  cases p with
  | nil => exact (hne rfl).elim
  | cons h p =>
    obtain ⟨_, k, hroot, _⟩ := h
    exact ⟨k, hroot⟩

/-- The large-component event is covered by finitely many labelled cluster
events with one coarse-scale coordinate and Q fine-scale coordinates. -/
theorem high_component_cluster (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hrh : r ≤ h)
    (x : V → d → ℝ) (root : V) (Q : ℕ) (hQ : 1 ≤ Q)
    (hcard : Q + 1 ≤ (reachableVertices (observationGraph (activeBlocks r h) x₀ r x) root).card) :
    ∃ v : Fin (Q + 1) → V, Function.Injective v ∧
      (∀ a, |x (v 0) a - x₀ a| ≤ (5 + 4 * Q) * h) ∧
      ∀ i a, |x (v i) a - x (v 0) a| ≤ 8 * r * Q := by
  obtain ⟨k, hk⟩ := large_component_root_incident (activeBlocks r h) x₀ r x root (by omega)
  obtain ⟨v, hv, hdist⟩ := observation_large_cluster (activeBlocks r h) x₀ r hr x root Q hcard
  refine ⟨v, hv, ?_, ?_⟩
  · intro a
    have hb := active_carrier_distance x₀ r h hr hrh k.val k.property (x root) hk a
    have ht := abs_sub_le (x (v 0) a) (x root a) (x₀ a)
    have hm := mul_le_mul_of_nonneg_right hrh (Nat.cast_nonneg Q : (0 : ℝ) ≤ Q)
    nlinarith [hdist 0 a]
  · intro i a
    have ht := abs_sub_le (x (v i) a) (x root a) (x (v 0) a)
    rw [abs_sub_comm (x root a) (x (v 0) a)] at ht
    linarith [hdist i a, hdist 0 a]

end ShellGeometry
end CausalLowerbound.PartB

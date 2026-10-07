import CausalLowerbound.PartC.CarrierLocalSigns
import CausalLowerbound.PartC.SharedSignIncidence
import CausalLowerbound.PartB.HighComponentGeometry
import CausalLowerbound.PartB.PhysicalComponentFactorization

/-! Geometry of the actual dependency graph, including the symbols read
by a carrier's centering and coefficient kernel. Enlarging the incidence
graph changes fixed constants but retains the coarse/fine cluster scales. -/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]

def physicalSharedIncidence (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h : ℝ)
    (x : V → d → ℝ) : V → S ⊕ activeBlocks (d := d) ℓ h → Prop :=
  sharedSignIncidence (fun i k => x i ∈ carrierBox x₀ r k.val)
    (fun i => physicalLocalSigns x₀ ℓ h (x i)) (fun k => carrierLocalSigns x₀ ℓ r h k.val)

def physicalSharedGraph (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h : ℝ)
    (x : V → d → ℝ) : SimpleGraph V := incidenceGraph (physicalSharedIncidence S x₀ ℓ r h x)

theorem physicalSharedIncidence_sign_witness (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h : ℝ) (hr : 0 < r) (x : V → d → ℝ) (i : V) (j : activeBlocks (d := d) ℓ h)
    (hij : physicalSharedIncidence S x₀ ℓ r h x i (Sum.inr j)) :
    ∃ y : d → ℝ, packet (coarseBump x₀ h) x₀ ℓ j.val y ≠ 0 ∧
      ∀ a, |x i a - y a| ≤ 4 * r := by
  rcases hij with hj | ⟨k, hik, hjk⟩
  · refine ⟨x i, ?_, fun a => by simp only [sub_self, abs_zero]; positivity⟩
    simpa only [physicalLocalSigns, Finset.mem_filter, Finset.mem_univ, true_and] using hj
  · obtain ⟨y, hy, hj⟩ := (mem_carrierLocalSigns x₀ ℓ r h k.val j).mp hjk
    refine ⟨y, ?_, fun a => common_carrier_distance x₀ r hr k.val (x i) y hik hy a⟩
    simpa only [physicalLocalSigns, Finset.mem_filter, Finset.mem_univ, true_and] using hj

theorem physicalSharedGraph_adj_distance (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hℓr : ℓ ≤ r) (x : V → d → ℝ)
    (i j : V) (hij : (physicalSharedGraph S x₀ ℓ r h x).Adj i j) (a : d) :
    |x i a - x j a| ≤ 10 * r := by
  obtain ⟨_, q, hi, hj⟩ := hij
  cases q with
  | inl k =>
    exact (common_carrier_distance x₀ r hr k.val (x i) (x j) hi hj a).trans (by linarith)
  | inr s =>
    obtain ⟨y, hy, hiy⟩ := physicalSharedIncidence_sign_witness S x₀ ℓ r h hr x i s hi
    obtain ⟨z, hz, hjz⟩ := physicalSharedIncidence_sign_witness S x₀ ℓ r h hr x j s hj
    have hn := packet_common_support_distance (coarseBump x₀ h) x₀ ℓ hℓ s.val y z hy hz
    have ha : |y a - z a| ≤ ‖y - z‖ := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (y - z) a
    have ht₁ := abs_sub_le (x i a) (y a) (z a)
    have ht₂ := abs_sub_le (x i a) (z a) (x j a)
    rw [abs_sub_comm (z a) (x j a)] at ht₂
    linarith [hiy a, hjz a]

theorem physicalSharedGraph_walk_distance (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hℓr : ℓ ≤ r) (x : V → d → ℝ)
    {i j : V} (p : (physicalSharedGraph S x₀ ℓ r h x).Walk i j) (a : d) :
    |x i a - x j a| ≤ 10 * r * p.length := by
  induction p with
  | nil => simp
  | @cons i j k hij p ih =>
    have hb := physicalSharedGraph_adj_distance S x₀ ℓ r h hℓ hr hℓr x i j hij a
    have ht := abs_sub_le (x i a) (x j a) (x k a)
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem physicalSharedGraph_large_cluster (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hℓr : ℓ ≤ r) (x : V → d → ℝ)
    (root : V) (Q : ℕ)
    (hcard : Q + 1 ≤ (reachableVertices (physicalSharedGraph S x₀ ℓ r h x) root).card) :
    ∃ v : Fin (Q + 1) → V, Function.Injective v ∧
      ∀ i a, |x (v i) a - x root a| ≤ 10 * r * Q := by
  obtain ⟨v, hv, hp⟩ := large_reachable_cluster (physicalSharedGraph S x₀ ℓ r h x) root Q hcard
  refine ⟨v, hv, fun i a => ?_⟩
  obtain ⟨p, hlen⟩ := hp i
  rw [abs_sub_comm]
  exact (physicalSharedGraph_walk_distance S x₀ ℓ r h hℓ hr hℓr x p a).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hlen) (by positivity))

theorem physicalSharedIncidence_coarse_bound (x₀ : d → ℝ) (ℓ r h : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hℓr : ℓ ≤ r) (hrh : r ≤ h) (x : V → d → ℝ)
    (i : V) (q : activeBlocks (d := d) r h ⊕ activeBlocks (d := d) ℓ h)
    (hi : physicalSharedIncidence (activeBlocks r h) x₀ ℓ r h x i q) (a : d) :
    |x i a - x₀ a| ≤ 5 * h := by
  cases q with
  | inl k => exact active_carrier_distance x₀ r h hr hrh k.val k.property (x i) hi a
  | inr j =>
    rcases hi with hj | ⟨k, hik, _⟩
    · have hp : packet (coarseBump x₀ h) x₀ ℓ j.val (x i) ≠ 0 := by
        simpa only [physicalLocalSigns, Finset.mem_filter, Finset.mem_univ, true_and] using hj
      have hx : x i ∈ carrierBox x₀ ℓ j.val := by
        by_contra hn
        exact hp (packet_zero_outside_carrier (coarseBump x₀ h) x₀ ℓ j.val (x i) hn)
      exact active_carrier_distance x₀ ℓ h hℓ (hℓr.trans hrh) j.val j.property (x i) hx a
    · exact active_carrier_distance x₀ r h hr hrh k.val k.property (x i) hik a

theorem physicalSharedGraph_high_component_cluster (x₀ : d → ℝ) (ℓ r h : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hℓr : ℓ ≤ r) (hrh : r ≤ h) (x : V → d → ℝ)
    (root : V) (Q : ℕ) (hQ : 1 ≤ Q)
    (hcard : Q + 1 ≤
      (reachableVertices (physicalSharedGraph (activeBlocks r h) x₀ ℓ r h x) root).card) :
    ∃ v : Fin (Q + 1) → V, Function.Injective v ∧
      (∀ a, |x (v 0) a - x₀ a| ≤ (5 + 10 * Q) * h) ∧
      ∀ i a, |x (v i) a - x (v 0) a| ≤ 20 * r * Q := by
  have hroot : ∃ q, physicalSharedIncidence (activeBlocks r h) x₀ ℓ r h x root q := by
    obtain ⟨v, hv, hne⟩ := Finset.exists_mem_ne (by omega : 1 <
      (reachableVertices (physicalSharedGraph (activeBlocks r h) x₀ ℓ r h x) root).card) root
    obtain ⟨p⟩ := (Finset.mem_filter.mp hv).2
    cases p with
    | nil => exact (hne rfl).elim
    | cons h p =>
      obtain ⟨_, q, hq, _⟩ := h
      exact ⟨q, hq⟩
  obtain ⟨q, hq⟩ := hroot
  obtain ⟨v, hv, hdist⟩ := physicalSharedGraph_large_cluster (activeBlocks r h)
    x₀ ℓ r h hℓ hr hℓr x root Q hcard
  refine ⟨v, hv, ?_, ?_⟩
  · intro a
    have hb := physicalSharedIncidence_coarse_bound x₀ ℓ r h hℓ hr hℓr hrh x root q hq a
    have ht := abs_sub_le (x (v 0) a) (x root a) (x₀ a)
    have hm := mul_le_mul_of_nonneg_right hrh (Nat.cast_nonneg Q : (0 : ℝ) ≤ Q)
    nlinarith [hdist 0 a]
  · intro i a
    have ht := abs_sub_le (x (v i) a) (x root a) (x (v 0) a)
    rw [abs_sub_comm (x root a) (x (v 0) a)] at ht
    linarith [hdist i a, hdist 0 a]

end CausalLowerbound.PartC

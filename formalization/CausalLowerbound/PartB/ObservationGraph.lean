import CausalLowerbound.PartB.CarrierLocalization
import Mathlib.Combinatorics.SimpleGraph.Path

/-! The actual observation incidence graph. Different connected components
use disjoint carrier labels; adjacency enforces a physical O(r) distance. -/
noncomputable section
set_option autoImplicit false
open scoped Classical
namespace CausalLowerbound.PartB
variable {V K : Type*}

def incidenceGraph (inc : V → K → Prop) : SimpleGraph V where
  Adj i j := i ≠ j ∧ ∃ k, inc i k ∧ inc j k
  symm := by rintro i j ⟨hne, k, hi, hj⟩; exact ⟨hne.symm, k, hj, hi⟩
  loopless := by intro i h; exact h.1 rfl

theorem common_label_same_component (inc : V → K → Prop) (i j : V) (k : K)
    (hi : inc i k) (hj : inc j k) :
    (incidenceGraph inc).connectedComponentMk i = (incidenceGraph inc).connectedComponentMk j := by
  by_cases he : i = j
  · rw [he]
  · exact SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable ⟨he, k, hi, hj⟩)

def componentLabels (inc : V → K → Prop) (c : (incidenceGraph inc).ConnectedComponent) : Set K :=
  {k | ∃ i, (incidenceGraph inc).connectedComponentMk i = c ∧ inc i k}

theorem componentLabels_disjoint (inc : V → K → Prop)
    (c c' : (incidenceGraph inc).ConnectedComponent) (hne : c ≠ c') :
    Disjoint (componentLabels inc c) (componentLabels inc c') := by
  apply Set.disjoint_left.mpr
  rintro k ⟨i, hi, hik⟩ ⟨j, hj, hjk⟩
  exact hne (hi.symm.trans ((common_label_same_component inc i j k hik hjk).trans hj))

namespace ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def observationGraph (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (x : V → d → ℝ) : SimpleGraph V :=
  incidenceGraph (fun i (k : S) => x i ∈ carrierBox x₀ r k.val)

theorem common_carrier_distance (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ)
    (x y : d → ℝ) (hx : x ∈ carrierBox x₀ r k) (hy : y ∈ carrierBox x₀ r k) (a : d) :
    |x a - y a| ≤ 4 * r := by
  have hx0 : (-2 : ℝ) ≤ (x a - x₀ a) / r - k a := hx.1 a
  have hx1 : (x a - x₀ a) / r - k a ≤ (2 : ℝ) := hx.2 a
  have hy0 : (-2 : ℝ) ≤ (y a - x₀ a) / r - k a := hy.1 a
  have hy1 : (y a - x₀ a) / r - k a ≤ (2 : ℝ) := hy.2 a
  have hh : |(x a - x₀ a) / r - (y a - x₀ a) / r| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
  have he : (x a - x₀ a) / r - (y a - x₀ a) / r = (x a - y a) / r := by ring
  rw [he, abs_div, abs_of_pos hr] at hh
  exact (div_le_iff₀ hr).mp hh

theorem observationGraph_adj_distance (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r)
    (x : V → d → ℝ) (i j : V) (hij : (observationGraph S x₀ r x).Adj i j) (a : d) :
    |x i a - x j a| ≤ 4 * r := by
  obtain ⟨_, k, hi, hj⟩ := hij
  exact common_carrier_distance x₀ r hr k.val (x i) (x j) hi hj a

theorem observationGraph_walk_distance (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r)
    (x : V → d → ℝ) {i j : V} (p : (observationGraph S x₀ r x).Walk i j) (a : d) :
    |x i a - x j a| ≤ 4 * r * p.length := by
  induction p with
  | nil => simp
  | @cons i j k hij p ih =>
    have h := observationGraph_adj_distance S x₀ r hr x i j hij a
    have ht := abs_sub_le (x i a) (x j a) (x k a)
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- A connected q-site configuration lies in a cube of radius 4 q r
around any chosen site. This can replace a spanning-tree integration. -/
theorem observationGraph_reachable_distance [Fintype V]
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (x : V → d → ℝ)
    (i j : V) (hij : (observationGraph S x₀ r x).Reachable i j) (a : d) :
    |x i a - x j a| ≤ 4 * r * Fintype.card V := by
  obtain ⟨p⟩ := hij
  have hb := observationGraph_walk_distance S x₀ r hr x p.toPath.val a
  have hn : (p.toPath.val.length : ℝ) ≤ Fintype.card V := by
    exact_mod_cast p.toPath.property.length_lt.le
  exact hb.trans (mul_le_mul_of_nonneg_left hn (by positivity))

end ShellGeometry
end CausalLowerbound.PartB

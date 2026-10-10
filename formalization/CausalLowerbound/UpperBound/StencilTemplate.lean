import CausalLowerbound.UpperBound.UniformStencil
import CausalLowerbound.PartB.ClusterVolume

/-! Fixed closed auxiliary boxes of positive volume.  All template parameters
depend only on the dimension and polynomial order. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open CausalLowerbound.PartB.ShellGeometry
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

structure StencilTemplate (d : Type*) [Fintype d] (p : ℕ) where
  radius : ℝ
  radius_pos : 0 < radius
  inverseBound : ℝ
  inverseBound_pos : 0 < inverseBound
  valid : ∀ z : TensorIndex d p → d → ℝ,
    (∀ j i, |z j i - gridNode p j i| ≤ radius) →
      (∀ j i, 0 < z j i ∧ z j i < 1) ∧
      IsUnit (tensorEvaluation p z).det ∧
      ∀ i, ∑ j, |(tensorEvaluation p z)⁻¹ i j| ≤ inverseBound

def standardStencilTemplate (d : Type*) [Fintype d] (p : ℕ) : StencilTemplate d p :=
  Classical.choice (by
    obtain ⟨δ, C, hδ, hC, h⟩ := exists_uniform_positive_stencil (d := d) p
    exact ⟨⟨δ, hδ, C, hC, h⟩⟩)

namespace StencilTemplate

variable {d : Type*} [Fintype d] {p : ℕ} (T : StencilTemplate d p)

def box (j : TensorIndex d p) : Set (d → ℝ) := coordinateBox (gridNode p j) T.radius

theorem mem_box (j : TensorIndex d p) (x : d → ℝ) :
    x ∈ T.box j ↔ ∀ i, |x i - gridNode p j i| ≤ T.radius :=
  mem_coordinateBox _ _ _

theorem center_mem_box (j : TensorIndex d p) : gridNode p j ∈ T.box j := by
  rw [T.mem_box]
  intro i
  simpa using T.radius_pos.le

theorem box_nonempty (j : TensorIndex d p) : (T.box j).Nonempty := ⟨_, T.center_mem_box j⟩

theorem box_isCompact (j : TensorIndex d p) : IsCompact (T.box j) := isCompact_Icc

theorem box_measurable (j : TensorIndex d p) : MeasurableSet (T.box j) :=
  isClosed_Icc.measurableSet

theorem box_volume (j : TensorIndex d p) :
    volume (T.box j) = ENNReal.ofReal (2 * T.radius) ^ Fintype.card d :=
  coordinateBox_volume _ _

theorem box_volume_pos (j : TensorIndex d p) : 0 < volume (T.box j) := by
  rw [T.box_volume]
  exact pos_iff_ne_zero.mpr (pow_ne_zero _
    (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos two_pos T.radius_pos)))

theorem box_volume_lt_top (j : TensorIndex d p) : volume (T.box j) < ⊤ := by
  rw [T.box_volume]
  exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

theorem valid_of_mem_boxes (z : TensorIndex d p → d → ℝ) (hz : ∀ j, z j ∈ T.box j) :
    (∀ j i, 0 < z j i ∧ z j i < 1) ∧
      IsUnit (tensorEvaluation p z).det ∧
      ∀ i, ∑ j, |(tensorEvaluation p z)⁻¹ i j| ≤ T.inverseBound :=
  T.valid z (fun j => (T.mem_box j (z j)).mp (hz j))

theorem box_positive (j : TensorIndex d p) {x : d → ℝ} (hx : x ∈ T.box j) :
    ∀ i, 0 < x i ∧ x i < 1 := by
  let z := Function.update (gridNode (d := d) p) j x
  have hz : ∀ k, z k ∈ T.box k := by
    intro k
    by_cases hk : k = j
    · simpa [z, hk] using hx
    · simpa only [z, Function.update_of_ne hk] using T.center_mem_box k
  simpa only [z, Function.update_self] using (T.valid_of_mem_boxes z hz).1 j

end StencilTemplate

end CausalLowerbound.UpperBound

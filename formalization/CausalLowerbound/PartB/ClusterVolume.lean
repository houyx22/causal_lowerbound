import CausalLowerbound.PartB.PhysicalDesign
import Mathlib.MeasureTheory.Constructions.Pi

/-! The volume of a labelled cluster: one coarse coordinate and Q
coordinates in fine boxes centred at the first observation. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace CausalLowerbound.PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def coordinateBox (x₀ : d → ℝ) (R : ℝ) : Set (d → ℝ) :=
  Set.Icc (fun a => x₀ a - R) (fun a => x₀ a + R)

theorem mem_coordinateBox (x₀ : d → ℝ) (R : ℝ) (x : d → ℝ) :
    x ∈ coordinateBox x₀ R ↔ ∀ a, |x a - x₀ a| ≤ R := by
  simp only [coordinateBox, Set.mem_Icc, Pi.le_def, abs_le]
  constructor
  · rintro ⟨hl, hu⟩ a
    constructor <;> linarith [hl a, hu a]
  · intro h
    constructor <;> intro a <;> have := h a <;> linarith

theorem coordinateBox_volume (x₀ : d → ℝ) (R : ℝ) :
    volume (coordinateBox x₀ R) = ENNReal.ofReal (2 * R) ^ Fintype.card d := by
  rw [coordinateBox, Real.volume_Icc_pi]
  simp only [show ∀ a, x₀ a + R - (x₀ a - R) = 2 * R by intro a; ring,
    Finset.prod_const, Finset.card_univ]

def rootedCluster (Q : ℕ) (x₀ : d → ℝ) (R L : ℝ) :
    Set ((d → ℝ) × (Fin Q → d → ℝ)) :=
  {z | z.1 ∈ coordinateBox x₀ R ∧ ∀ i, z.2 i ∈ coordinateBox z.1 L}

theorem rootedCluster_measurable (Q : ℕ) (x₀ : d → ℝ) (R L : ℝ) :
    MeasurableSet (rootedCluster Q x₀ R L) := by
  simp only [rootedCluster, mem_coordinateBox, Set.setOf_and, Set.setOf_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro a
    exact (isClosed_le (by fun_prop) continuous_const).measurableSet
  · apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro a
    exact (isClosed_le (by fun_prop) continuous_const).measurableSet

theorem rootedCluster_volume (Q : ℕ) (x₀ : d → ℝ) (R L : ℝ) :
    volume (rootedCluster Q x₀ R L) =
      ENNReal.ofReal (2 * R) ^ Fintype.card d *
        ENNReal.ofReal (2 * L) ^ (Q * Fintype.card d) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (rootedCluster_measurable Q x₀ R L)]
  have hs (x : d → ℝ) :
      (Prod.mk x ⁻¹' rootedCluster Q x₀ R L) =
        if x ∈ coordinateBox x₀ R then Set.univ.pi (fun _ : Fin Q => coordinateBox x L) else ∅ := by
    ext y
    by_cases hx : x ∈ coordinateBox x₀ R <;> simp [rootedCluster, hx]
  simp_rw [hs]
  have hm (x : d → ℝ) :
      volume (if x ∈ coordinateBox x₀ R then Set.univ.pi (fun _ : Fin Q => coordinateBox x L) else ∅) =
        (coordinateBox x₀ R).indicator (fun _ => ENNReal.ofReal (2 * L) ^ (Q * Fintype.card d)) x := by
    by_cases hx : x ∈ coordinateBox x₀ R
    · rw [if_pos hx, Set.indicator_of_mem hx]
      change (Measure.pi (fun _ : Fin Q => (volume : Measure (d → ℝ))))
        (Set.univ.pi (fun _ : Fin Q => coordinateBox x L)) = _
      rw [Measure.pi_pi]
      simp only [coordinateBox_volume, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← pow_mul, Nat.mul_comm]
    · simp [hx]
  simp_rw [hm]
  rw [lintegral_indicator_const
    (show MeasurableSet (coordinateBox x₀ R) from measurableSet_Icc), coordinateBox_volume]
  exact mul_comm _ _

def labelledCluster (Q : ℕ) (x₀ : d → ℝ) (R L : ℝ) : Set (Fin (Q + 1) → d → ℝ) :=
  (fun x => (x 0, fun i : Fin Q => x i.succ)) ⁻¹' rootedCluster Q x₀ R L

theorem labelledCluster_measurable (Q : ℕ) (x₀ : d → ℝ) (R L : ℝ) :
    MeasurableSet (labelledCluster Q x₀ R L) := by
  exact (rootedCluster_measurable Q x₀ R L).preimage
    ((measurable_pi_apply 0).prodMk (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.succ)))

theorem labelledCluster_volume (Q : ℕ) (x₀ : d → ℝ) (R L : ℝ) :
    volume (labelledCluster Q x₀ R L) =
      ENNReal.ofReal (2 * R) ^ Fintype.card d *
        ENNReal.ofReal (2 * L) ^ (Q * Fintype.card d) := by
  have hp := volume_preserving_piFinSuccAbove (fun _ : Fin (Q + 1) => d → ℝ) 0
  have he := hp.measure_preimage_equiv (rootedCluster Q x₀ R L)
  change volume (labelledCluster Q x₀ R L) = volume (rootedCluster Q x₀ R L) at he
  rw [he, rootedCluster_volume]

end CausalLowerbound.PartB.ShellGeometry

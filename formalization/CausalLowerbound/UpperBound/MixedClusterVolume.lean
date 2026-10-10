import CausalLowerbound.PartB.ClusterVolume

/-! Exact mixed-scale cluster volumes.  Offsets and radii may differ between
roles.  A fixed non-anchor observation also bounds the volume available for
the missing anchor, which is useful for every overlap pattern. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open CausalLowerbound.PartB.ShellGeometry
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.UpperBound

variable {d I : Type*} [Fintype d] [Fintype I]

def mixedCluster (A : Set (d → ℝ)) (shift : I → d → ℝ) (radius : I → ℝ) :
    Set ((d → ℝ) × (I → d → ℝ)) :=
  {z | z.1 ∈ A ∧ ∀ i, z.2 i ∈ coordinateBox (z.1 + shift i) (radius i)}

theorem mixedCluster_measurable (A : Set (d → ℝ)) (hA : MeasurableSet A)
    (shift : I → d → ℝ) (radius : I → ℝ) :
    MeasurableSet (mixedCluster A shift radius) := by
  simp only [mixedCluster, mem_coordinateBox, Set.setOf_and, Set.setOf_forall]
  apply MeasurableSet.inter (hA.preimage measurable_fst)
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro a
  exact (isClosed_le (by fun_prop) continuous_const).measurableSet

theorem mixedCluster_volume (A : Set (d → ℝ)) (hA : MeasurableSet A)
    (shift : I → d → ℝ) (radius : I → ℝ) :
    volume (mixedCluster A shift radius) =
      volume A * ∏ i, ENNReal.ofReal (2 * radius i) ^ Fintype.card d := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (mixedCluster_measurable A hA shift radius)]
  have hs (x : d → ℝ) :
      Prod.mk x ⁻¹' mixedCluster A shift radius =
        if x ∈ A then Set.univ.pi (fun i => coordinateBox (x + shift i) (radius i)) else ∅ := by
    ext y
    by_cases hx : x ∈ A <;> simp [mixedCluster, hx]
  simp_rw [hs]
  have hm (x : d → ℝ) :
      volume (if x ∈ A then Set.univ.pi (fun i => coordinateBox (x + shift i) (radius i)) else ∅) =
        A.indicator (fun _ => ∏ i, ENNReal.ofReal (2 * radius i) ^ Fintype.card d) x := by
    by_cases hx : x ∈ A
    · rw [if_pos hx, Set.indicator_of_mem hx]
      change (Measure.pi (fun _ : I => (volume : Measure (d → ℝ))))
        (Set.univ.pi (fun i => coordinateBox (x + shift i) (radius i))) = _
      rw [Measure.pi_pi]
      simp only [coordinateBox_volume]
    · simp [hx]
  simp_rw [hm]
  rw [lintegral_indicator_const hA, mul_comm]

theorem mixedCluster_volume_box (c : d → ℝ) (R : ℝ)
    (shift : I → d → ℝ) (radius : I → ℝ) :
    volume (mixedCluster (coordinateBox c R) shift radius) =
      ENNReal.ofReal (2 * R) ^ Fintype.card d *
        ∏ i, ENNReal.ofReal (2 * radius i) ^ Fintype.card d := by
  rw [mixedCluster_volume (coordinateBox c R) (show MeasurableSet (coordinateBox c R)
    from measurableSet_Icc), coordinateBox_volume]

/-- Restriction on the anchor imposed by an already observed role. -/
theorem mem_coordinateBox_iff_anchor (x y b : d → ℝ) (R : ℝ) :
    y ∈ coordinateBox (x + b) R ↔ x ∈ coordinateBox (y - b) R := by
  simp only [mem_coordinateBox, Pi.add_apply, Pi.sub_apply]
  apply forall_congr'
  intro a
  rw [show x a - (y a - b a) = -(y a - (x a + b a)) by ring, abs_neg]

def anchorSupport (A : Set (d → ℝ)) (fixed shift : I → d → ℝ) (radius : I → ℝ) :
    Set (d → ℝ) := {x | x ∈ A ∧ ∀ i, fixed i ∈ coordinateBox (x + shift i) (radius i)}

theorem anchorSupport_measurable (A : Set (d → ℝ)) (hA : MeasurableSet A)
    (fixed shift : I → d → ℝ) (radius : I → ℝ) :
    MeasurableSet (anchorSupport A fixed shift radius) := by
  simp only [anchorSupport, mem_coordinateBox_iff_anchor, Set.setOf_and, Set.setOf_forall]
  exact hA.inter (MeasurableSet.iInter (fun _ => measurableSet_Icc))

omit [Fintype d] [Fintype I] in
theorem anchorSupport_subset (A : Set (d → ℝ))
    (fixed shift : I → d → ℝ) (radius : I → ℝ) :
    anchorSupport A fixed shift radius ⊆ A := fun _ hx => hx.1

omit [Fintype I] in
theorem anchorSupport_volume_le_fixed (A : Set (d → ℝ))
    (fixed shift : I → d → ℝ) (radius : I → ℝ) (i : I) :
    volume (anchorSupport A fixed shift radius) ≤
      ENNReal.ofReal (2 * radius i) ^ Fintype.card d := by
  rw [← coordinateBox_volume (fixed i - shift i)]
  apply measure_mono
  intro x hx
  exact (mem_coordinateBox_iff_anchor x (fixed i) (shift i) (radius i)).mp (hx.2 i)

theorem mixedCompletion_volume_le {J : Type*} [Fintype J]
    (A : Set (d → ℝ)) (hA : MeasurableSet A)
    (fixed fixedShift : I → d → ℝ) (fixedRadius : I → ℝ)
    (missingShift : J → d → ℝ) (missingRadius : J → ℝ) (i : I) :
    volume (mixedCluster (anchorSupport A fixed fixedShift fixedRadius)
      missingShift missingRadius) ≤
      ENNReal.ofReal (2 * fixedRadius i) ^ Fintype.card d *
        ∏ j, ENNReal.ofReal (2 * missingRadius j) ^ Fintype.card d := by
  rw [mixedCluster_volume _ (anchorSupport_measurable A hA fixed fixedShift fixedRadius)]
  exact mul_le_mul_right' (anchorSupport_volume_le_fixed A fixed fixedShift fixedRadius i) _

end CausalLowerbound.UpperBound

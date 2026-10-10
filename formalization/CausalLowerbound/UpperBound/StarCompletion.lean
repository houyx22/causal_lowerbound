import CausalLowerbound.UpperBound.CoordinateSplit
import CausalLowerbound.UpperBound.MixedClusterVolume
import CausalLowerbound.UpperBound.SplitSample

/-! Completion volumes for an arbitrary shared-role set in a star-shaped
cluster.  A shared anchor gives a product of missing-box volumes.  If the
anchor is missing, any shared role restricts the anchor to a reflected box. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open CausalLowerbound.PartB.ShellGeometry
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.UpperBound

variable {I d Z : Type*} [Fintype I] [DecidableEq I] [Fintype d] [MeasurableSpace Z]

omit [Fintype d] in
theorem joinRoles_apply_shared (S : Finset I) (x : {i // i ∈ S} → Z)
    (y : {i // i ∉ S} → Z) (i : I) (hi : i ∈ S) : joinRoles S (x, y) i = x ⟨i, hi⟩ := by
  simp [joinRoles, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]

omit [Fintype d] in
theorem joinRoles_apply_missing (S : Finset I) (x : {i // i ∈ S} → Z)
    (y : {i // i ∉ S} → Z) (i : I) (hi : i ∉ S) : joinRoles S (x, y) i = y ⟨i, hi⟩ := by
  simp [joinRoles, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hi]

def starCluster (a : I) (A : Set (d → ℝ)) (shift : I → d → ℝ) (radius : I → ℝ) :
    Set (I → d → ℝ) :=
  {X | X a ∈ A ∧ ∀ i, i ≠ a → X i ∈ coordinateBox (X a + shift i) (radius i)}

theorem starCluster_eq_mixedCluster (a : I) (A : Set (d → ℝ))
    (shift : I → d → ℝ) (radius : I → ℝ) :
    starCluster a A shift radius = coordinateSplit a ⁻¹'
      mixedCluster A (fun i : {i : I // i ≠ a} => shift i) (fun i => radius i) := by
  ext X
  simp [starCluster, mixedCluster, coordinateSplit]

theorem starCluster_measurable (a : I) (A : Set (d → ℝ)) (hA : MeasurableSet A)
    (shift : I → d → ℝ) (radius : I → ℝ) : MeasurableSet (starCluster a A shift radius) := by
  rw [starCluster_eq_mixedCluster]
  exact (mixedCluster_measurable A hA _ _).preimage (coordinateSplit a).measurable

theorem starCluster_volume (a : I) (A : Set (d → ℝ)) (hA : MeasurableSet A)
    (shift : I → d → ℝ) (radius : I → ℝ) :
    volume (starCluster a A shift radius) =
      volume A * ∏ i : {i : I // i ≠ a}, ENNReal.ofReal (2 * radius i) ^ Fintype.card d := by
  rw [starCluster_eq_mixedCluster, (coordinateSplit_volume_preserving a).measure_preimage_equiv,
    mixedCluster_volume A hA]

theorem starCompletion_volume_shared_anchor (a : I) (A : Set (d → ℝ))
    (shift : I → d → ℝ) (radius : I → ℝ) (S : Finset I) (ha : a ∈ S)
    (x : {i // i ∈ S} → d → ℝ) :
    volume {y | joinRoles S (x, y) ∈ starCluster a A shift radius} ≤
      ∏ i : {i // i ∉ S}, ENNReal.ofReal (2 * radius i) ^ Fintype.card d := by
  calc
    _ ≤ volume (Set.univ.pi (fun i : {i // i ∉ S} =>
        coordinateBox (x ⟨a, ha⟩ + shift i) (radius i))) := by
      apply measure_mono
      intro y hy i _
      have hia : (i : I) ≠ a := fun he => i.property (he.symm ▸ ha)
      have h := hy.2 i hia
      rw [joinRoles_apply_shared S x y a ha, joinRoles_apply_missing S x y i i.property] at h
      exact h
    _ = _ := by
      change (Measure.pi (fun _ : {i // i ∉ S} => (volume : Measure (d → ℝ)))) _ = _
      rw [Measure.pi_pi]
      simp only [coordinateBox_volume]

theorem starCompletion_volume_missing_anchor (a : I) (A : Set (d → ℝ))
    (shift : I → d → ℝ) (radius : I → ℝ) (S : Finset I) (ha : a ∉ S)
    (x : {i // i ∈ S} → d → ℝ) (j : {i // i ∈ S}) :
    volume {y | joinRoles S (x, y) ∈ starCluster a A shift radius} ≤
      ENNReal.ofReal (2 * radius j) ^ Fintype.card d *
        ∏ i : {i : {i // i ∉ S} // i ≠ ⟨a, ha⟩},
          ENNReal.ofReal (2 * radius i.val.val) ^ Fintype.card d := by
  let a' : {i // i ∉ S} := ⟨a, ha⟩
  have hja : (j : I) ≠ a := fun he => ha (he ▸ j.property)
  calc
    _ ≤ volume (starCluster a' (coordinateBox (x j - shift j) (radius j))
        (fun i : {i // i ∉ S} => shift i) (fun i => radius i)) := by
      apply measure_mono
      intro y hy
      constructor
      · have h := hy.2 j hja
        rw [joinRoles_apply_shared S x y j j.property, joinRoles_apply_missing S x y a ha] at h
        exact (mem_coordinateBox_iff_anchor (y a') (x j) (shift j) (radius j)).mp h
      · intro i hi
        have hia : (i : I) ≠ a := fun he => hi (Subtype.ext he)
        have h := hy.2 i hia
        rw [joinRoles_apply_missing S x y i i.property, joinRoles_apply_missing S x y a ha] at h
        exact h
    _ = _ := by
      rw [starCluster_volume a' (coordinateBox (x j - shift j) (radius j))
        (show MeasurableSet (coordinateBox (x j - shift j) (radius j)) from measurableSet_Icc),
        coordinateBox_volume]

end CausalLowerbound.UpperBound

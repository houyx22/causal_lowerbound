import CausalLowerbound.PartB.TorusTaper
import CausalLowerbound.PartB.TaperBadVolume

/-! Transport of the proved collision-volume bound to the compact torus
on which the actual coefficient posterior and ghost integral live. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped BigOperators Classical ENNReal
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] Real.fact_zero_lt_one
attribute [local instance] finOrderedDecEq finOrderedDecLt
local instance taperVolumeCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance taperVolumeCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance taperVolumeCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {d J : Type*} [Fintype d] [DecidableEq d] [Fintype J]

theorem torusProjection_cube_preserving :
    MeasurePreserving (torusProjection (α := d)) (cubeMeasure d) (volume : Measure (Torus d)) := by
  have he : unitCell (α := d) =ᵐ[volume] Set.Icc (0 : d → ℝ) 1 := by
    simpa only [unitCell, volume_pi] using
      (Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : d => (volume : Measure ℝ))
        (f := (0 : d → ℝ)) (g := 1))
  change MeasurePreserving _ (volume.restrict (Set.Icc (0 : d → ℝ) 1)) _
  rw [← Measure.restrict_congr_set he]
  exact torusProjection_measurePreserving

theorem torusProjection_pi_cube_preserving :
    MeasurePreserving (fun u : J → d → ℝ => fun i => torusProjection (u i))
      (Measure.pi (fun _ : J => cubeMeasure d)) (volume : Measure (J → Torus d)) :=
  measurePreserving_pi (fun _ => cubeMeasure d) (fun _ => volume)
    (fun _ => torusProjection_cube_preserving)

theorem torusTaper_bad_volume [Nonempty d] (q : ℕ) (s : ℝ)
    (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (t : ℝ) (ht : 0 < t) :
    volume.real {u : Fin (q + 1) → Torus d | torusTaper (q + 1) t u ≠ 1} ≤
      (q + 1 : ℝ) * ((2 * t) ^ s * collisionMomentBound d s ^ q) := by
  have hb : MeasurableSet {u : Fin (q + 1) → Torus d | torusTaper (q + 1) t u ≠ 1} :=
    (isClosed_singleton.preimage (torusTaper_continuous (q + 1) t)).measurableSet.compl
  have he := (torusProjection_pi_cube_preserving (d := d) (J := Fin (q + 1))).measure_preimage
    hb.nullMeasurableSet
  have hl (u : Fin (q + 1) → d → ℝ) := torusTaper_lift (q + 1) t (fun a => u a.1 a.2)
  have hpre : (fun u : Fin (q + 1) → d → ℝ => fun i => torusProjection (u i)) ⁻¹'
      {u | torusTaper (q + 1) t u ≠ 1} =
      {u | completeTaper (q + 1) t (fun a => u a.1 a.2) ≠ 1} := by
    ext u
    change _ ≠ 1 ↔ _ ≠ 1
    exact not_congr (congrArg (fun x : ℝ => x = 1) (hl u)).to_iff
  rw [hpre] at he
  change (volume {u : Fin (q + 1) → Torus d | torusTaper (q + 1) t u ≠ 1}).toReal ≤ _
  rw [← he]
  have hbound := complete_taper_bad_volume (d := d) q s hs hsd t ht
  exact hbound

end CausalLowerbound.PartB.ShellGeometry

import CausalLowerbound.PartB.StarCollisionVolume
import CausalLowerbound.PartB.CompleteGraph

/-! A concrete bad-configuration bound for the complete-graph taper.
This version allows an arbitrarily small loss in the dimension exponent. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical ENNReal
namespace CausalLowerbound.PartB.ShellGeometry
open ConfigurationShells
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def vertexStarProduct (q : ℕ) (u : Fin (q + 1) → d → ℝ) (i : Fin (q + 1)) : ℝ :=
  starDistanceProduct (u i) (fun j : Fin q => u (i.succAbove j))

theorem completeVertexProduct_eq_star (q : ℕ) (u : Fin (q + 1) → d → ℝ) (i : Fin (q + 1)) :
    completeVertexProduct i (fun p => u p.1 p.2) = vertexStarProduct q u i := by
  unfold completeVertexProduct vertexStarProduct starDistanceProduct
  have he := (finSuccAboveEquiv i).prod_comp
    (fun j : {j : Fin (q + 1) // j ≠ i} => truncatedDistance (u i) (u j.val))
  change (∏ j : {j : Fin (q + 1) // j ≠ i}, truncatedDistance (u i) (u j.val)) = _
  rw [← he]
  apply Finset.prod_congr rfl
  intro j _
  exact truncatedDistance_symm _ _

theorem vertexStarProduct_sublevel_volume [Nonempty d] (q : ℕ) (i : Fin (q + 1))
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (R : ℝ) (hR : 0 < R) :
    (Measure.pi (fun _ : Fin (q + 1) => cubeMeasure d)).real {u | vertexStarProduct q u i ≤ R} ≤
      R ^ s * collisionMomentBound d s ^ q := by
  let μ := cubeMeasure d
  let ν := Measure.pi (fun _ : Fin q => μ)
  let bad : Set ((d → ℝ) × (Fin q → d → ℝ)) := {p | starDistanceProduct p.1 p.2 ≤ R}
  have hc : Continuous (fun p : (d → ℝ) × (Fin q → d → ℝ) => starDistanceProduct p.1 p.2) := by
    have hcj (j : Fin q) : Continuous (fun p : (d → ℝ) × (Fin q → d → ℝ) =>
        truncatedDistance (p.2 j) p.1) := by
      have hm : Continuous (fun p : (d → ℝ) × (Fin q → d → ℝ) => (p.2 j, p.1)) :=
        ((continuous_apply j).comp continuous_snd).prodMk continuous_fst
      have hh := (truncatedDistance_continuous (d := d)).comp hm
      exact hh
    exact continuous_finset_prod _ (fun j _ => hcj j)
  have hb : MeasurableSet bad := measurableSet_le hc.measurable measurable_const
  have he : Measure.pi (fun _ : Fin (q + 1) => μ) {u | vertexStarProduct q u i ≤ R} =
      μ.prod ν bad := by
    exact (measurePreserving_piFinSuccAbove (fun _ : Fin (q + 1) => μ) i).measure_preimage hb.nullMeasurableSet
  have hbound : μ.prod ν bad ≤ ENNReal.ofReal (R ^ s * collisionMomentBound d s ^ q) := by
    rw [Measure.prod_apply hb]
    calc
      _ ≤ ∫⁻ _v, ENNReal.ofReal (R ^ s * collisionMomentBound d s ^ q) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict (μ := (volume : Measure (d → ℝ))) measurableSet_Icc] with v hv
        have h := starDistanceProduct_sublevel_volume (J := Fin q) s hs hsd v hv R hR
        change ν.real {u | starDistanceProduct v u ≤ R} ≤ _ at h
        change ν {u | starDistanceProduct v u ≤ R} ≤ _
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal (by simpa using h)
      _ = _ := by simp
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (he.le.trans hbound)
  simpa [measureReal_def, μ, ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hR.le _)
    (pow_nonneg (collisionMomentBound_nonneg (d := d) s) _))] using h

theorem configuration_star_bad_volume [Nonempty d] (q : ℕ) (s : ℝ)
    (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (R : ℝ) (hR : 0 < R) :
    (Measure.pi (fun _ : Fin (q + 1) => cubeMeasure d)).real
      {u | ∃ i, vertexStarProduct q u i ≤ R} ≤
      (q + 1 : ℝ) * (R ^ s * collisionMomentBound d s ^ q) := by
  have he : {u : Fin (q + 1) → d → ℝ | ∃ i, vertexStarProduct q u i ≤ R} =
      ⋃ i, {u | vertexStarProduct q u i ≤ R} := by ext u; simp
  rw [he]
  calc
    _ ≤ ∑ i : Fin (q + 1), (Measure.pi (fun _ : Fin (q + 1) => cubeMeasure d)).real
        {u | vertexStarProduct q u i ≤ R} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin (q + 1), R ^ s * collisionMomentBound d s ^ q :=
      Finset.sum_le_sum (fun i _ => vertexStarProduct_sublevel_volume q i s hs hsd R hR)
    _ = _ := by simp [Nat.cast_add, Nat.cast_one]

theorem complete_taper_bad_subset (q : ℕ) (t : ℝ) (ht : 0 < t) :
    {u : Fin (q + 1) → d → ℝ | graphTaper edgeLeft edgeRight taperCutoff t
      (graphDistance edgeLeft edgeRight (fun p => u p.1 p.2)) ≠ 1} ⊆
        {u | ∃ i, vertexStarProduct q u i ≤ 2 * t} := by
  intro u hu
  by_contra h
  change ¬ ∃ i, vertexStarProduct q u i ≤ 2 * t at h
  apply hu
  push_neg at h
  apply Finset.prod_eq_one
  intro i _
  apply taperCutoff_one
  rw [vertexProduct_complete, completeVertexProduct_eq_star]
  exact (le_div_iff₀ ht).mpr (h i).le

theorem complete_taper_bad_volume [Nonempty d] (q : ℕ) (s : ℝ)
    (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (t : ℝ) (ht : 0 < t) :
    (Measure.pi (fun _ : Fin (q + 1) => cubeMeasure d)).real
      {u : Fin (q + 1) → d → ℝ | graphTaper edgeLeft edgeRight taperCutoff t
        (graphDistance edgeLeft edgeRight (fun p => u p.1 p.2)) ≠ 1} ≤
      (q + 1 : ℝ) * ((2 * t) ^ s * collisionMomentBound d s ^ q) :=
  (measureReal_mono (complete_taper_bad_subset q t ht)).trans
    (configuration_star_bad_volume q s hs hsd (2 * t) (by positivity))

end CausalLowerbound.PartB.ShellGeometry

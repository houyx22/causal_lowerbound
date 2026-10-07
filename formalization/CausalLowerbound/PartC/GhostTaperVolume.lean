import CausalLowerbound.PartC.GhostTaperRemoval

/-! The ghost-taper cost used by the observation estimate has a concrete
subcritical volume bound. Both retained and ghost coordinates are integrated
against their actual product cube measures. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype G]

theorem completedGhostTaperDefect_joint_integrable (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ) :
    Integrable (fun v => 1 - completedCubeTaper (d := d) Q e τ v)
      ((Measure.pi (fun _ : I => cubeMeasure d)).prod (Measure.pi (fun _ : G => cubeMeasure d))) := by
  apply (integrable_const (1 : ℝ)).mono'
    (continuous_const.sub (completedCubeTaper_continuous Q e τ)).aestronglyMeasurable
  filter_upwards [] with v
  have h := completedCubeTaper_bounds (d := d) Q e τ v
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h.2)]
  linarith

theorem completedGhostTaperDefect_integrable (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ) :
    Integrable (completedGhostTaperDefect (d := d) Q e τ) (Measure.pi (fun _ : I => cubeMeasure d)) :=
  (completedGhostTaperDefect_joint_integrable Q e τ).integral_prod_left

theorem completedGhostTaperDefect_volume_bound [Nonempty d]
    (q : ℕ) (e : I ⊕ G ≃ Fin (q + 1)) (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ))
    (τ : ℝ) (hτ : 0 < τ) :
    (∫ u : I → d → ℝ, completedGhostTaperDefect (q + 1) e τ u ∂Measure.pi (fun _ : I => cubeMeasure d)) ≤
      (q + 1 : ℝ) * ((2 * τ) ^ s * collisionMomentBound d s ^ q) := by
  let μ := (Measure.pi (fun _ : I => cubeMeasure d)).prod (Measure.pi (fun _ : G => cubeMeasure d))
  let bad := {v : (I → d → ℝ) × (G → d → ℝ) | completedCubeTaper (q + 1) e τ v ≠ 1}
  have hb : MeasurableSet bad := (isClosed_singleton.preimage
    (completedCubeTaper_continuous (d := d) (q + 1) e τ)).measurableSet.compl
  have hi := completedGhostTaperDefect_joint_integrable (d := d) (q + 1) e τ
  have he : (∫ u : I → d → ℝ, completedGhostTaperDefect (q + 1) e τ u
      ∂Measure.pi (fun _ : I => cubeMeasure d)) =
      ∫ v, 1 - completedCubeTaper (q + 1) e τ v ∂μ := (integral_prod _ hi).symm
  rw [he]
  calc
    _ ≤ ∫ v, bad.indicator (fun _ => (1 : ℝ)) v ∂μ := by
      apply integral_mono hi ((integrable_const (1 : ℝ)).indicator hb)
      intro v
      by_cases hv : v ∈ bad
      · rw [Set.indicator_of_mem hv]
        change 1 - completedCubeTaper (q + 1) e τ v ≤ 1
        linarith [(completedCubeTaper_bounds (d := d) (q + 1) e τ v).1]
      · have hχ : completedCubeTaper (q + 1) e τ v = 1 := by
          simpa only [bad, Set.mem_setOf_eq, not_not] using hv
        simp only [Set.indicator_of_not_mem hv, hχ, sub_self, le_refl]
    _ = μ.real bad := by rw [integral_indicator hb]; simp [measureReal_def]
    _ ≤ _ := completedCubeTaper_bad_volume q e s hs hsd τ hτ

end CausalLowerbound.PartC

import CausalLowerbound.PartC.UnitCubeGhosts
import CausalLowerbound.PartB.TorusTaper
import CausalLowerbound.PartB.TaperBadVolume

/-! The complete-graph taper on a retained/ghost split of real unit-cube
coordinates, with exact transport of its subcritical bad-volume bound. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {X I G V d : Type*} [Fintype I] [Fintype G] [Fintype V] [Fintype d] [DecidableEq d]

theorem completedSites_measurePreserving [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (e : I ⊕ G ≃ V) :
    MeasurePreserving (fun v : (I → X) × (G → X) => completedSites e v.1 v.2)
      ((Measure.pi (fun _ : I => μ)).prod (Measure.pi (fun _ : G => μ)))
      (Measure.pi (fun _ : V => μ)) := by
  have hm := (measurePreserving_piCongrLeft (fun _ : V => μ) e).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : I ⊕ G => μ))
  have hmap : (MeasurableEquiv.piCongrLeft (fun _ : V => X) e) ∘
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : I ⊕ G => X)).symm =
      (fun v : (I → X) × (G → X) => completedSites e v.1 v.2) := by
    funext v i
    simp only [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.piCongrLeft_apply_eq_cast,
      cast_eq, Equiv.sumPiEquivProdPi_symm_apply, completedSites]
    cases e.symm i <;> rfl
  rw [hmap] at hm
  exact hm

def completedCubeTaper (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ)
    (v : (I → d → ℝ) × (G → d → ℝ)) : ℝ :=
  completeTaper Q τ (completedConfiguration e v.1 v.2)

theorem completedCubeTaper_continuous (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ) :
    Continuous (completedCubeTaper (d := d) Q e τ) := by
  apply (completeTaper_continuous Q τ).comp
  apply continuous_pi
  intro p
  change Continuous (fun v : (I → d → ℝ) × (G → d → ℝ) => (Sum.elim v.1 v.2 (e.symm p.1)) p.2)
  cases he : e.symm p.1 with
  | inl i =>
    simp only [he, Sum.elim_inl]
    exact (continuous_apply p.2).comp ((continuous_apply i).comp continuous_fst)
  | inr i =>
    simp only [he, Sum.elim_inr]
    exact (continuous_apply p.2).comp ((continuous_apply i).comp continuous_snd)

theorem completedCubeTaper_bounds (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ)
    (v : (I → d → ℝ) × (G → d → ℝ)) :
    0 ≤ completedCubeTaper Q e τ v ∧ completedCubeTaper Q e τ v ≤ 1 := by
  simpa only [torusTaper_lift] using torusTaper_bounds Q τ
    (fun i => torusProjection (configurationSite (completedConfiguration e v.1 v.2) i))

theorem completedCubeTaper_bad_volume [Nonempty d] (q : ℕ) (e : I ⊕ G ≃ Fin (q + 1))
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (τ : ℝ) (hτ : 0 < τ) :
    ((Measure.pi (fun _ : I => cubeMeasure d)).prod (Measure.pi (fun _ : G => cubeMeasure d))).real
      {v : (I → d → ℝ) × (G → d → ℝ) | completedCubeTaper (q + 1) e τ v ≠ 1} ≤
      (q + 1 : ℝ) * ((2 * τ) ^ s * collisionMomentBound d s ^ q) := by
  have hc : Continuous (fun u : Fin (q + 1) → d → ℝ => completeTaper (q + 1) τ (fun p => u p.1 p.2)) :=
    (completeTaper_continuous (q + 1) τ).comp
      (continuous_pi (fun p => (continuous_apply p.2).comp (continuous_apply p.1)))
  have hb : MeasurableSet {u : Fin (q + 1) → d → ℝ | completeTaper (q + 1) τ (fun p => u p.1 p.2) ≠ 1} :=
    (isClosed_singleton.preimage hc).measurableSet.compl
  have he := (completedSites_measurePreserving (cubeMeasure d) e).measure_preimage hb.nullMeasurableSet
  change ((Measure.pi (fun _ : I => cubeMeasure d)).prod (Measure.pi (fun _ : G => cubeMeasure d)))
      {v | completedCubeTaper (q + 1) e τ v ≠ 1} =
    (Measure.pi (fun _ : Fin (q + 1) => cubeMeasure d))
      {u | completeTaper (q + 1) τ (fun p => u p.1 p.2) ≠ 1} at he
  rw [measureReal_def, he]
  exact complete_taper_bad_volume q s hs hsd τ hτ

end CausalLowerbound.PartC

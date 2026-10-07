import CausalLowerbound.PartC.GhostTaperRemoval
import CausalLowerbound.PartB.GhostReindex
import CausalLowerbound.PartB.PhysicalGhostLeakage

/-! Identify the unweighted cube ghost defect with the zero-density-
perturbation instance of the existing torus ghost law. This proves exact
reindexing invariance and transfers the physical-box volume estimate. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells
attribute [local instance] finOrderedDecEq finOrderedDecLt Real.fact_zero_lt_one
local instance defectCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance defectCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance defectCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {d I I' G G' : Type*} [Fintype d] [DecidableEq d]
  [Fintype I] [Fintype I'] [Fintype G] [Fintype G']

theorem densityMoment_zero (H : DiscreteLaw ℕ) (Q : ℕ) (u : I → Torus d) :
    densityMoment H Q 0 u = 1 := by
  have he := densityMoment_bounds H Q 0 (by norm_num) (by norm_num) u
  norm_num only [sub_zero, add_zero, one_pow] at he
  exact le_antisymm he.2 he.1

theorem completedCubeTaper_eq_torus (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ)
    (u : I → d → ℝ) (z : G → d → ℝ) :
    completedCubeTaper Q e τ (u, z) =
      completedTorusTaper Q e τ ((fun i => torusProjection (u i)), (fun g => torusProjection (z g))) := by
  rw [completedCubeTaper, ← torusTaper_lift]
  congr 1
  funext i
  change torusProjection (Sum.elim u z (e.symm i)) =
    Sum.elim (fun i => torusProjection (u i)) (fun g => torusProjection (z g)) (e.symm i)
  cases e.symm i <;> rfl

theorem completedGhostTaperDefect_eq_ghostActivation (H : DiscreteLaw ℕ)
    (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ) (u : I → d → ℝ) :
    completedGhostTaperDefect Q e τ u =
      1 - ghostActivation H Q 0 (completedTorusTaper Q e τ) (fun i => torusProjection (u i)) := by
  let f := fun z : G → Torus d =>
    1 - completedTorusTaper Q e τ ((fun i => torusProjection (u i)), z)
  have hf : Continuous f := continuous_const.sub
    ((completedTorusTaper_continuous Q e τ).comp (continuous_const.prodMk continuous_id))
  have he := ghost_leakage_identity H Q 0 (by norm_num) (by norm_num)
    (completedTorusTaper Q e τ) (completedTorusTaper_continuous Q e τ) (fun i => torusProjection (u i))
  simp only [completedDensity, densityMoment_zero, one_mul] at he
  unfold completedGhostTaperDefect
  simp_rw [completedCubeTaper_eq_torus]
  exact (torusProjection_pi_cube_integral f hf).trans he.symm

theorem completedGhostTaperDefect_reindex
    (Q : ℕ) (τ : ℝ) (e : I ⊕ G ≃ Fin Q) (e' : I' ⊕ G' ≃ Fin Q)
    (a : I ≃ I') (b : G ≃ G') (u : I' → d → ℝ) :
    completedGhostTaperDefect Q e τ (u ∘ a) = completedGhostTaperDefect Q e' τ u := by
  let H : DiscreteLaw ℕ := DiscreteLaw.ofPMF (PMF.pure 0)
  rw [completedGhostTaperDefect_eq_ghostActivation H, completedGhostTaperDefect_eq_ghostActivation H]
  exact congrArg (fun t : ℝ => 1 - t)
    (ghostActivation_reindex H Q 0 τ e e' a b (fun i => torusProjection (u i)))

theorem completedGhostTaperDefect_continuous (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ) :
    Continuous (completedGhostTaperDefect (d := d) Q e τ) := by
  let H : DiscreteLaw ℕ := DiscreteLaw.ofPMF (PMF.pure 0)
  have he := funext (completedGhostTaperDefect_eq_ghostActivation (d := d) H Q e τ)
  rw [he]
  exact continuous_const.sub ((ghostActivation_continuous H Q 0 (by norm_num) (by norm_num)
    _ (completedTorusTaper_continuous Q e τ)).comp
    (continuous_pi (fun i => torusProjection_quotient.continuous.comp (continuous_apply i))))

theorem completedGhostTaperDefect_physical_volume [Nonempty d]
    (q : ℕ) (e : I ⊕ G ≃ Fin (q + 1)) (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ))
    (τ : ℝ) (hτ : 0 < τ) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ) :
    (∫ x in carrierConfigurationBox (K := I) x₀ r k,
      completedGhostTaperDefect (q + 1) e τ
        (fun i => carrierCoordinate (localCoordinate x₀ r k (x i)))) ≤
      (4 * r) ^ (Fintype.card I * Fintype.card d) *
        ((q + 1 : ℝ) * ((2 * τ) ^ s * collisionMomentBound d s ^ q)) := by
  let H : DiscreteLaw ℕ := DiscreteLaw.ofPMF (PMF.pure 0)
  simp_rw [completedGhostTaperDefect_eq_ghostActivation H]
  simpa only [add_zero, sub_zero, one_pow, one_mul, div_one] using
    physical_ghost_leakage H q e 0 (by norm_num) (by norm_num) s hs hsd τ hτ x₀ r hr k

end CausalLowerbound.PartC

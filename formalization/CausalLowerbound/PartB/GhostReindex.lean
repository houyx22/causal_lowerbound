import CausalLowerbound.PartB.ConcreteGhostLeakage

/-! Exact invariance of the posterior and averaged taper under retained
site reindexing, ghost reindexing, and the choice of completion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener ConfigurationShells
attribute [local instance] finOrderedDecEq finOrderedDecLt Real.fact_zero_lt_one
local instance reindexCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance reindexCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance reindexCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {d K K' G G' Ω : Type*} [Fintype d] [DecidableEq d]
  [Fintype K] [Fintype K'] [Fintype G] [Fintype G'] [Fintype Ω]

theorem coefficientPosterior_equiv (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (e : K ≃ K') (u : K' → Torus d) :
    coefficientPosterior H kernel Q θ hθ hθ1 (u ∘ e) =
      coefficientPosterior H kernel Q θ hθ hθ1 u := by
  unfold coefficientPosterior
  congr 1
  apply DiscreteLaw.ext
  intro label
  simp only [DiscreteLaw.tilt, densityTensor_equiv]

theorem torusTaper_permute (Q : ℕ) (ε : ℝ) (u : Fin Q → Torus d) (σ : Equiv.Perm (Fin Q)) :
    torusTaper Q ε (u ∘ σ) = torusTaper Q ε u := by
  let v : Fin Q × d → ℝ := fun a => torusRepresentative (u a.1) a.2
  have hu : (fun i => torusProjection (configurationSite v i)) = u := by
    funext i
    exact torusProjection_representative (u i)
  have huσ : (fun i => torusProjection (configurationSite (permuteConfiguration σ v) i)) = u ∘ σ := by
    funext i
    exact torusProjection_representative (u (σ i))
  have hv := torusTaper_lift Q ε v
  have hp := torusTaper_lift Q ε (permuteConfiguration σ v)
  rw [hu] at hv
  rw [huσ] at hp
  rw [hp, hv]
  exact complete_graphTaper_permute σ ε v

theorem completedTorusTaper_reindex (Q : ℕ) (ε : ℝ)
    (e : K ⊕ G ≃ Fin Q) (e' : K' ⊕ G' ≃ Fin Q) (a : K ≃ K') (b : G ≃ G')
    (u : K' → Torus d) (z : G' → Torus d) :
    completedTorusTaper Q e ε (u ∘ a, z ∘ b) = completedTorusTaper Q e' ε (u, z) := by
  let σ : Equiv.Perm (Fin Q) := (e.symm.trans (Equiv.sumCongr a b)).trans e'
  have he : (Sum.elim (u ∘ a) (z ∘ b) ∘ e.symm) =
      (Sum.elim u z ∘ e'.symm) ∘ σ := by
    funext i
    simp only [Function.comp_apply, σ, Equiv.trans_apply, Equiv.symm_apply_apply]
    cases e.symm i <;> rfl
  unfold completedTorusTaper
  rw [he, torusTaper_permute]

theorem completedDensity_reindex (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (a : K ≃ K') (b : G ≃ G') (u : K' → Torus d) (z : G' → Torus d) :
    completedDensity H Q θ (u ∘ a, z ∘ b) = completedDensity H Q θ (u, z) := by
  have he : Sum.elim (u ∘ a) (z ∘ b) = (Sum.elim u z) ∘ Equiv.sumCongr a b := by
    funext i
    cases i <;> rfl
  unfold completedDensity
  rw [he, densityMoment_equiv]

theorem ghostActivation_reindex (H : DiscreteLaw ℕ) (Q : ℕ) (θ ε : ℝ)
    (e : K ⊕ G ≃ Fin Q) (e' : K' ⊕ G' ≃ Fin Q) (a : K ≃ K') (b : G ≃ G')
    (u : K' → Torus d) :
    ghostActivation H Q θ (completedTorusTaper Q e ε) (u ∘ a) =
      ghostActivation H Q θ (completedTorusTaper Q e' ε) u := by
  unfold ghostActivation
  rw [densityMoment_equiv]
  congr 1
  have hp := volume_measurePreserving_piCongrLeft (fun _ : G => Torus d) b.symm
  have he := hp.integral_comp' (fun z : G → Torus d =>
    completedDensity H Q θ (u ∘ a, z) * completedTorusTaper Q e ε (u ∘ a, z))
  have hf (z : G' → Torus d) :
      (MeasurableEquiv.piCongrLeft (fun _ : G => Torus d) b.symm) z = z ∘ b := by
    funext i
    simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, Equiv.symm_symm, cast_eq]
    rfl
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Function.comp_apply, hf]
  rw [completedDensity_reindex H Q θ a b, completedTorusTaper_reindex Q ε e e' a b]

end CausalLowerbound.PartB.ShellGeometry

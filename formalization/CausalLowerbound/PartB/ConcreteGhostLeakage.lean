import CausalLowerbound.PartB.EvaluatedCarrier
import CausalLowerbound.PartB.TorusTaperVolume

/-! Quantitative ghost leakage for the constructed complete-graph taper.
The exponent s may be chosen arbitrarily close to the spatial dimension. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] Real.fact_zero_lt_one
local instance concreteGhostCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance concreteGhostCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance concreteGhostCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {d K G : Type*} [Fintype d] [DecidableEq d] [Fintype K] [Fintype G]
local instance : BorelSpace (K → Torus d) := Pi.borelSpace
local instance : BorelSpace (G → Torus d) := Pi.borelSpace
local instance : OpensMeasurableSpace ((K → Torus d) × (G → Torus d)) := Prod.opensMeasurableSpace

theorem ghostActivation_continuous (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (χ : (K → Torus d) × (G → Torus d) → ℝ) (hc : Continuous χ) :
    Continuous (ghostActivation H Q θ χ) := by
  have hn : Continuous (fun u : K → Torus d =>
      ∫ z : G → Torus d, completedDensity H Q θ (u, z) * χ (u, z)) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        ((completedDensity_continuous H Q θ hθ hθ1).mul hc) isCompact_univ)
  exact hn.div (densityMoment_continuous H Q θ hθ hθ1)
    (fun u => (densityMoment_pos H Q θ hθ hθ1 u).ne')

theorem completedTorusTaper_bad_volume [Nonempty d] (q : ℕ) (e : K ⊕ G ≃ Fin (q + 1))
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (t : ℝ) (ht : 0 < t) :
    volume.real {x : (K → Torus d) × (G → Torus d) | completedTorusTaper (q + 1) e t x ≠ 1} ≤
      (q + 1 : ℝ) * ((2 * t) ^ s * collisionMomentBound d s ^ q) := by
  have hm := (volume_measurePreserving_piCongrLeft (fun _ : Fin (q + 1) => Torus d) e).comp
    (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : K ⊕ G => Torus d))
  have hmap : (MeasurableEquiv.piCongrLeft (fun _ : Fin (q + 1) => Torus d) e) ∘
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : K ⊕ G => Torus d)).symm =
      (fun x : (K → Torus d) × (G → Torus d) => Sum.elim x.1 x.2 ∘ e.symm) := by
    funext x i
    simp only [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.piCongrLeft_apply_eq_cast,
      cast_eq, Equiv.sumPiEquivProdPi_symm_apply]
    cases e.symm i <;> rfl
  rw [hmap] at hm
  have hb : MeasurableSet {u : Fin (q + 1) → Torus d | torusTaper (q + 1) t u ≠ 1} :=
    (isClosed_singleton.preimage (torusTaper_continuous (q + 1) t)).measurableSet.compl
  have he := hm.measure_preimage hb.nullMeasurableSet
  change volume {x : (K → Torus d) × (G → Torus d) | completedTorusTaper (q + 1) e t x ≠ 1} =
    volume {u : Fin (q + 1) → Torus d | torusTaper (q + 1) t u ≠ 1} at he
  change (volume _).toReal ≤ _
  rw [he]
  exact torusTaper_bad_volume q s hs hsd t ht

theorem concrete_weighted_ghost_leakage [Nonempty d] (H : DiscreteLaw ℕ) (q : ℕ)
    (e : K ⊕ G ≃ Fin (q + 1)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (t : ℝ) (ht : 0 < t) :
    (∫ u : K → Torus d, densityMoment H (q + 1) θ u *
      (1 - ghostActivation H (q + 1) θ (completedTorusTaper (q + 1) e t) u)) ≤
      (1 + θ) ^ (q + 1) * ((q + 1 : ℝ) * ((2 * t) ^ s * collisionMomentBound d s ^ q)) := by
  have hc := Fintype.card_congr e
  rw [Fintype.card_fin] at hc
  have h := ghost_leakage_volume_bound H (q + 1) θ hθ hθ1
    (completedTorusTaper (d := d) (q + 1) e t) (completedTorusTaper_continuous _ _ _)
    (completedTorusTaper_bounds _ _ _)
  rw [hc] at h
  exact h.trans (mul_le_mul_of_nonneg_left (completedTorusTaper_bad_volume q e s hs hsd t ht)
    (pow_nonneg (by linarith) _))

theorem concrete_ghost_leakage [Nonempty d] (H : DiscreteLaw ℕ) (q : ℕ)
    (e : K ⊕ G ≃ Fin (q + 1)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (t : ℝ) (ht : 0 < t) :
    (∫ u : K → Torus d, 1 - ghostActivation H (q + 1) θ (completedTorusTaper (q + 1) e t) u) ≤
      ((1 + θ) ^ (q + 1) * ((q + 1 : ℝ) * ((2 * t) ^ s * collisionMomentBound d s ^ q))) /
        (1 - θ) ^ Fintype.card K := by
  let χ := completedTorusTaper (d := d) (q + 1) e t
  let f := fun u : K → Torus d => 1 - ghostActivation H (q + 1) θ χ u
  have hf : Continuous f := continuous_const.sub
    (ghostActivation_continuous H (q + 1) θ hθ hθ1 χ (completedTorusTaper_continuous _ _ _))
  have hf0 (u : K → Torus d) : 0 ≤ f u := sub_nonneg.mpr
    (ghostActivation_bounds H (q + 1) θ hθ hθ1 χ (completedTorusTaper_continuous _ _ _)
      (completedTorusTaper_bounds _ _ _) u).2
  have hi : Integrable f (volume : Measure (K → Torus d)) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdi : Integrable (fun u => densityMoment H (q + 1) θ u * f u) (volume : Measure (K → Torus d)) :=
    ((densityMoment_continuous H (q + 1) θ hθ hθ1).mul hf).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  apply (le_div_iff₀ (pow_pos (sub_pos.mpr hθ1) _)).mpr
  rw [mul_comm, ← integral_const_mul]
  apply (integral_mono (hi.const_mul _) hdi (fun u => mul_le_mul_of_nonneg_right
    (densityMoment_bounds H (q + 1) θ hθ hθ1 u).1 (hf0 u))).trans
  exact concrete_weighted_ghost_leakage H q e θ hθ hθ1 s hs hsd t ht

end CausalLowerbound.PartB.ShellGeometry

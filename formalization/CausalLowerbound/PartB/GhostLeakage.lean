import CausalLowerbound.PartB.CarrierProjectivity

/-! The averaged taper and its exact ghost-leakage identity, for the actual
countable density carrier. The geometric estimate of the bad set is separate. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] Real.fact_zero_lt_one
local instance ghostCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance ghostCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance ghostCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {d K G : Type*} [Fintype d] [DecidableEq d] [Fintype K] [Fintype G]
local instance : BorelSpace (K → Torus d) := Pi.borelSpace
local instance : BorelSpace (G → Torus d) := Pi.borelSpace
local instance : OpensMeasurableSpace ((K → Torus d) × (G → Torus d)) := Prod.opensMeasurableSpace

def completedDensity (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (x : (K → Torus d) × (G → Torus d)) : ℝ := densityMoment H Q θ (Sum.elim x.1 x.2)

theorem completedDensity_continuous (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) : Continuous (completedDensity (K := K) (G := G) (d := d) H Q θ) := by
  apply (densityMoment_continuous H Q θ hθ hθ1).comp
  apply continuous_pi
  intro i
  cases i with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr i => exact (continuous_apply i).comp continuous_snd

def ghostActivation (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (χ : (K → Torus d) × (G → Torus d) → ℝ) (u : K → Torus d) : ℝ :=
  (∫ z : G → Torus d, completedDensity H Q θ (u, z) * χ (u, z)) / densityMoment H Q θ u

theorem ghostActivation_bounds (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (χ : (K → Torus d) × (G → Torus d) → ℝ) (hc : Continuous χ)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (u : K → Torus d) :
    0 ≤ ghostActivation H Q θ χ u ∧ ghostActivation H Q θ χ u ≤ 1 := by
  have hd := densityMoment_pos H Q θ hθ hθ1 u
  have hf := (completedDensity_continuous (K := K) (G := G) (d := d) H Q θ hθ hθ1).comp
    ((continuous_const : Continuous (fun _ : G → Torus d => u)).prodMk continuous_id)
  have hg := hc.comp ((continuous_const : Continuous (fun _ : G → Torus d => u)).prodMk continuous_id)
  have hi : Integrable (fun z : G → Torus d => completedDensity H Q θ (u, z)) volume :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hij : Integrable (fun z : G → Torus d => completedDensity H Q θ (u, z) * χ (u, z)) volume :=
    (hf.mul hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  constructor
  · exact div_nonneg (integral_nonneg (fun z => mul_nonneg
      (densityMoment_pos H Q θ hθ hθ1 _).le (hχ (u, z)).1)) hd.le
  · apply (div_le_one hd).mpr
    calc
      _ ≤ ∫ z : G → Torus d, completedDensity H Q θ (u, z) := by
        apply integral_mono hij hi
        intro z
        exact mul_le_of_le_one_right (densityMoment_pos H Q θ hθ hθ1 _).le (hχ (u, z)).2
      _ = _ := densityMoment_projective H Q θ hθ hθ1 u

theorem ghost_leakage_identity (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (χ : (K → Torus d) × (G → Torus d) → ℝ) (hc : Continuous χ) (u : K → Torus d) :
    densityMoment H Q θ u * (1 - ghostActivation H Q θ χ u) =
      ∫ z : G → Torus d, completedDensity H Q θ (u, z) * (1 - χ (u, z)) := by
  have hf := (completedDensity_continuous (K := K) (G := G) (d := d) H Q θ hθ hθ1).comp
    ((continuous_const : Continuous (fun _ : G → Torus d => u)).prodMk continuous_id)
  have hg := hc.comp ((continuous_const : Continuous (fun _ : G → Torus d => u)).prodMk continuous_id)
  have hi : Integrable (fun z : G → Torus d => completedDensity H Q θ (u, z)) volume :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hij : Integrable (fun z : G → Torus d => completedDensity H Q θ (u, z) * χ (u, z)) volume :=
    (hf.mul hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [mul_sub, mul_one]
  have hproj : (∫ z : G → Torus d, completedDensity H Q θ (u, z)) = densityMoment H Q θ u :=
    densityMoment_projective H Q θ hθ hθ1 u
  rw [integral_sub hi hij, hproj]
  unfold ghostActivation
  field_simp [(densityMoment_pos H Q θ hθ hθ1 u).ne']

theorem integrated_ghost_leakage (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (χ : (K → Torus d) × (G → Torus d) → ℝ) (hc : Continuous χ) :
    (∫ u : K → Torus d, densityMoment H Q θ u * (1 - ghostActivation H Q θ χ u)) =
      ∫ x : (K → Torus d) × (G → Torus d), completedDensity H Q θ x * (1 - χ x) := by
  simp_rw [ghost_leakage_identity H Q θ hθ hθ1 χ hc]
  exact (integral_prod _ (((completedDensity_continuous H Q θ hθ hθ1).mul
    (continuous_const.sub hc)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm

theorem ghost_leakage_volume_bound (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (χ : (K → Torus d) × (G → Torus d) → ℝ) (hc : Continuous χ)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    (∫ u : K → Torus d, densityMoment H Q θ u * (1 - ghostActivation H Q θ χ u)) ≤
      (1 + θ) ^ Fintype.card (K ⊕ G) * volume.real {x | χ x ≠ 1} := by
  rw [integrated_ghost_leakage H Q θ hθ hθ1 χ hc]
  let bad := {x : (K → Torus d) × (G → Torus d) | χ x ≠ 1}
  have hb : MeasurableSet bad := (isClosed_singleton.preimage hc).measurableSet.compl
  have hi : Integrable (fun x : (K → Torus d) × (G → Torus d) => completedDensity H Q θ x * (1 - χ x)) volume :=
    ((completedDensity_continuous H Q θ hθ hθ1).mul
      (continuous_const.sub hc)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x, bad.indicator (fun _ => (1 + θ) ^ Fintype.card (K ⊕ G)) x := by
      apply integral_mono hi ((integrable_const _).indicator hb)
      intro x
      by_cases hx : x ∈ bad
      · rw [Set.indicator_of_mem hx]
        exact (mul_le_of_le_one_right (densityMoment_pos H Q θ hθ hθ1 _).le
          (by linarith [(hχ x).1])).trans (densityMoment_bounds H Q θ hθ hθ1 _).2
      · have he : χ x = 1 := by simpa only [bad, Set.mem_setOf_eq, not_not] using hx
        simp [Set.indicator_of_not_mem hx, he]
    _ = _ := by rw [integral_indicator hb]; simp [mul_comm, bad, measureReal_def]

end CausalLowerbound.PartB.ShellGeometry



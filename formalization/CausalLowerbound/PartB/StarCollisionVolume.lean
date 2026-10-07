import CausalLowerbound.PartB.CollisionInverseMoment
import Mathlib.MeasureTheory.Integral.Pi

/-! Bad-volume bounds for a star of actual periodic distances. For every
0 < s < d the product sublevel has measure at most C R^s, uniformly in
the root. The argument integrates all other sites independently. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
variable {d J : Type*} [Fintype d] [DecidableEq d] [Fintype J]

def starDistanceProduct (v : d → ℝ) (u : J → d → ℝ) : ℝ :=
  ∏ j, truncatedDistance (u j) v

theorem starDistanceProduct_continuous (v : d → ℝ) :
    Continuous (starDistanceProduct (J := J) v) := by
  have hc (j : J) : Continuous (fun u : J → d → ℝ => truncatedDistance (u j) v) := by
    have hm : Continuous (fun u : J → d → ℝ => (u j, v)) :=
      (continuous_apply j).prodMk continuous_const
    have hh := (truncatedDistance_continuous (d := d)).comp hm
    exact hh
  exact continuous_finset_prod _ (fun j _ => hc j)

theorem starDistanceProduct_nonneg (v : d → ℝ) (u : J → d → ℝ) :
    0 ≤ starDistanceProduct v u :=
  Finset.prod_nonneg (fun j _ => (truncatedDistance_range (u j) v).1)

theorem starInverseMoment_integrable (s : ℝ) (hs : 0 < s)
    (hsd : s < (Fintype.card d : ℝ)) (v : d → ℝ)
    (hv : v ∈ Set.Icc (0 : d → ℝ) 1) :
    Integrable (fun u : J → d → ℝ => ∏ j, collisionInverseMoment s v (u j))
      (Measure.pi (fun _ : J => cubeMeasure d)) := by
  exact @Integrable.fintype_prod ℝ inferInstance J inferInstance (d → ℝ)
    (fun _ => collisionInverseMoment s v) ⟨cubeMeasure d⟩
    (inferInstanceAs (SigmaFinite (cubeMeasure d)))
    (fun _ => (collisionInverseMoment_integrable s hs hsd v hv).1)

theorem starInverseMoment_integral_bound (s : ℝ) (hs : 0 < s)
    (hsd : s < (Fintype.card d : ℝ)) (v : d → ℝ)
    (hv : v ∈ Set.Icc (0 : d → ℝ) 1) :
    (∫ u : J → d → ℝ, (∏ j, collisionInverseMoment s v (u j))
      ∂Measure.pi (fun _ : J => cubeMeasure d)) ≤ collisionMomentBound d s ^ Fintype.card J := by
  have he := @integral_fintype_prod_eq_prod ℝ inferInstance J inferInstance (fun _ => d → ℝ)
    (fun _ => collisionInverseMoment s v) (fun _ => ⟨cubeMeasure d⟩)
    (fun _ => inferInstanceAs (SigmaFinite (cubeMeasure d)))
  change (∫ u : J → d → ℝ, (∏ j, collisionInverseMoment s v (u j))
    ∂Measure.pi (fun _ : J => cubeMeasure d)) =
    ∏ _ : J, ∫ u, collisionInverseMoment s v u ∂cubeMeasure d at he
  rw [he, Finset.prod_const, Finset.card_univ]
  exact pow_le_pow_left₀ (integral_nonneg (collisionInverseMoment_nonneg s v))
    (collisionInverseMoment_integrable s hs hsd v hv).2 _

theorem starDistanceProduct_pos_ae [Nonempty d] (v : d → ℝ)
    (hv : v ∈ Set.Icc (0 : d → ℝ) 1) :
    ∀ᵐ u : J → d → ℝ ∂Measure.pi (fun _ : J => cubeMeasure d), 0 < starDistanceProduct v u := by
  have he (j : J) : ∀ᵐ u : J → d → ℝ ∂Measure.pi (fun _ : J => cubeMeasure d),
      truncatedDistance (u j) v ≠ 0 := by
    have hh : ∀ᵐ w ∂cubeMeasure d, truncatedDistance w v ≠ 0 :=
      ae_iff.mpr (by simpa using truncatedDistance_zero_null v hv)
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : J => cubeMeasure d) (i := j)).eventually hh
  filter_upwards [Filter.eventually_all.mpr he] with u hu
  exact Finset.prod_pos (fun j _ => lt_of_le_of_ne (truncatedDistance_range (u j) v).1 (hu j).symm)

theorem starDistanceProduct_sublevel_volume [Nonempty d] (s : ℝ) (hs : 0 < s)
    (hsd : s < (Fintype.card d : ℝ)) (v : d → ℝ)
    (hv : v ∈ Set.Icc (0 : d → ℝ) 1) (R : ℝ) (hR : 0 < R) :
    (Measure.pi (fun _ : J => cubeMeasure d)).real {u | starDistanceProduct v u ≤ R} ≤
      R ^ s * collisionMomentBound d s ^ Fintype.card J := by
  let μ := Measure.pi (fun _ : J => cubeMeasure d)
  let bad := {u : J → d → ℝ | starDistanceProduct v u ≤ R}
  have hbad : MeasurableSet bad := measurableSet_le (starDistanceProduct_continuous v).measurable measurable_const
  have hi := starInverseMoment_integrable (J := J) s hs hsd v hv
  have hpoint : ∀ᵐ u ∂μ, bad.indicator (fun _ => (1 : ℝ)) u ≤
      R ^ s * ∏ j, collisionInverseMoment s v (u j) := by
    filter_upwards [starDistanceProduct_pos_ae (J := J) v hv] with u hu
    by_cases hb : u ∈ bad
    · rw [Set.indicator_of_mem hb]
      have he : (∏ j, collisionInverseMoment s v (u j)) = starDistanceProduct v u ^ (-s) := by
        exact Real.finset_prod_rpow _ _ (fun j _ => (truncatedDistance_range (u j) v).1) _
      rw [he, Real.rpow_neg hu.le]
      have hpow := Real.rpow_le_rpow hu.le (show starDistanceProduct v u ≤ R from hb) hs.le
      have hn : starDistanceProduct v u ^ s ≠ 0 := (Real.rpow_pos_of_pos hu s).ne'
      calc
        (1 : ℝ) = starDistanceProduct v u ^ s * (starDistanceProduct v u ^ s)⁻¹ :=
          (mul_inv_cancel₀ hn).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr (Real.rpow_nonneg hu.le _))
    · rw [Set.indicator_of_not_mem hb]
      exact mul_nonneg (Real.rpow_nonneg hR.le _) (Finset.prod_nonneg
        (fun j _ => collisionInverseMoment_nonneg s v (u j)))
  have h := integral_mono_ae ((integrable_const (1 : ℝ)).indicator hbad) (hi.const_mul (R ^ s)) hpoint
  have hind : (∫ u, bad.indicator (fun _ => (1 : ℝ)) u ∂μ) = μ.real bad := by
    rw [integral_indicator hbad]
    simp [measureReal_def]
  rw [hind, integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (starInverseMoment_integral_bound (J := J) s hs hsd v hv)
    (Real.rpow_nonneg hR.le _))

end CausalLowerbound.PartB.ShellGeometry

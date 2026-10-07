import CausalLowerbound.DiscreteIndependence

/-! Group countably supported independent labels by fibers of a finite
map. Equality of singleton probabilities verifies the actual product law. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.DiscreteLaw
variable {K C : Type*} [Fintype K] [Fintype C] [DecidableEq C]

theorem toMeasure_singleton {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : DiscreteLaw Ω) (x : Ω) : μ.toMeasure {x} = ENNReal.ofReal (μ.weight x) :=
  PMF.toMeasure_apply_singleton μ.toPMF x (measurableSet_singleton x)

def labelGrouping (c : K → C) : (K → ℕ) ≃ᵐ ((a : C) → ({k // c k = a} → ℕ)) where
  toFun x a k := x k.val
  invFun y k := y (c k) ⟨k, rfl⟩
  left_inv _ := rfl
  right_inv y := by
    funext a ⟨k, hk⟩
    subst a
    rfl
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _

theorem independent_grouping_weight (μ : K → DiscreteLaw ℕ) (c : K → C)
    (y : (a : C) → ({k // c k = a} → ℕ)) :
    (independent μ).weight ((labelGrouping c).symm y) =
      ∏ a, (independent (fun k : {k // c k = a} => μ k.val)).weight (y a) := by
  simp only [independent_weight]
  calc
    _ = ∏ a, ∏ k : {k // c k = a}, (μ k.val).weight ((labelGrouping c).symm y k.val) :=
      (Fintype.prod_fiberwise c (fun k => (μ k).weight ((labelGrouping c).symm y k))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro a _
      apply Finset.prod_congr rfl
      intro ⟨k, hk⟩ _
      subst a
      rfl

theorem measurePreserving_labelGrouping (μ : K → DiscreteLaw ℕ) (c : K → C) :
    MeasurePreserving (labelGrouping c) (independent μ).toMeasure
      (Measure.pi (fun a => (independent (fun k : {k // c k = a} => μ k.val)).toMeasure)) := by
  refine ⟨(labelGrouping c).measurable, Measure.ext_of_singleton (fun y => ?_)⟩
  have hp : (labelGrouping c) ⁻¹' {y} = {(labelGrouping c).symm y} := by
    ext x
    change (labelGrouping c) x = y ↔ x = (labelGrouping c).symm y
    constructor
    · intro he
      rw [← he, (labelGrouping c).symm_apply_apply]
    · intro he
      rw [he, (labelGrouping c).apply_symm_apply]
  rw [Measure.map_apply (labelGrouping c).measurable (measurableSet_singleton y),
    hp, toMeasure_singleton,
    independent_grouping_weight, ← Set.univ_pi_singleton y, Measure.pi_pi]
  simp only [toMeasure_singleton]
  exact ENNReal.ofReal_prod_of_nonneg (fun a _ => (independent (fun k : {k // c k = a} => μ k.val)).nonneg _)

theorem expect_independent_component_prod (μ : K → DiscreteLaw ℕ) (c : K → C)
    (f : (a : C) → ({k // c k = a} → ℕ) → ℝ)
    (B : C → ℝ) (hb : ∀ a x, |f a x| ≤ B a) :
    (independent μ).expect (fun x => ∏ a, f a (fun k => x k.val)) =
      ∏ a, (independent (fun k : {k // c k = a} => μ k.val)).expect (f a) := by
  have hprod (x : K → ℕ) : |∏ a, f a (fun k => x k.val)| ≤ ∏ a, B a := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun a _ => hb a _)
  rw [← integral_eq_expect _ _ (integrable_bounded (independent μ) _ _ hprod)]
  have hgroup := (measurePreserving_labelGrouping μ c).integral_comp' (fun y => ∏ a, f a (y a))
  change (∫ x, ∏ a, f a (fun k => x k.val) ∂(independent μ).toMeasure) =
    ∫ y, ∏ a, f a (y a)
      ∂Measure.pi (fun a => (independent (fun k : {k // c k = a} => μ k.val)).toMeasure) at hgroup
  rw [hgroup]
  have he := @integral_fintype_prod_eq_prod ℝ inferInstance C inferInstance
    (fun a => {k // c k = a} → ℕ) f
    (fun a => ⟨(independent (fun k : {k // c k = a} => μ k.val)).toMeasure⟩)
    (fun a => inferInstanceAs (SigmaFinite (independent (fun k : {k // c k = a} => μ k.val)).toMeasure))
  change (∫ y, ∏ a, f a (y a)
      ∂Measure.pi (fun a => (independent (fun k : {k // c k = a} => μ k.val)).toMeasure)) =
    ∏ a, ∫ x, f a x ∂(independent (fun k : {k // c k = a} => μ k.val)).toMeasure at he
  rw [he]
  apply Finset.prod_congr rfl
  intro a _
  exact integral_eq_expect _ _ (integrable_bounded _ (f a) (B a) (hb a))

end CausalLowerbound.DiscreteLaw

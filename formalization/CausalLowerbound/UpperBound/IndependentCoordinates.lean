import CausalLowerbound.UpperBound.Covariance
import CausalLowerbound.FiniteProductMeasures
import Mathlib.Probability.Integration

/-! Coordinate marginals and covariances for a product of possibly different
probability laws.  This includes the conditional response laws at a fixed
tuple of covariates. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.UpperBound

variable {I J Z : Type*} [Fintype I] [Fintype J] [MeasurableSpace Z]

theorem coordinateSelection_family_measurePreserving
    (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)]
    (e : J → I) (he : Function.Injective e) :
    MeasurePreserving (fun x : I → Z => fun j => x (e j))
      (Measure.pi μ) (Measure.pi (fun j => μ (e j))) := by
  let p : I → Prop := fun i => i ∈ Set.range e
  letI : Fintype (Subtype p) := Subtype.fintype p
  let E : J ≃ Subtype p := Equiv.ofInjective e he
  have hs := measurePreserving_piEquivPiSubtypeProd μ p
  have hf : MeasurePreserving Prod.fst
      ((Measure.pi (fun i : Subtype p => μ i)).prod
        (Measure.pi (fun i : {i // ¬ p i} => μ i)))
      (Measure.pi (fun i : Subtype p => μ i)) := by
    refine ⟨measurable_fst, ?_⟩
    simp
  have hr := measurePreserving_piCongrLeft (fun j : J => μ (e j)) E.symm
  have hν : (fun i : Subtype p => μ (e (E.symm i))) = (fun i : Subtype p => μ i) := by
    funext i
    exact congrArg μ (congrArg Subtype.val (E.apply_symm_apply i))
  rw [hν] at hr
  convert hr.comp (hf.comp hs) using 1
  funext x j
  simp [Function.comp_def, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft', MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd, E]
  rfl

omit [Fintype J] in
theorem coordinate_eval_measurePreserving
    (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)] (i : I) :
    MeasurePreserving (fun z : I → Z => z i) (Measure.pi μ) (μ i) := by
  have he : Function.Injective (fun _ : Unit => i) := fun _ _ _ => Subsingleton.elim _ _
  have h := coordinateSelection_family_measurePreserving μ (fun _ : Unit => i) he
  exact (measurePreserving_funUnique (μ i) Unit).comp h

omit [Fintype J] in
theorem coordinate_pair_measurePreserving
    (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)] (i j : I) (hij : i ≠ j) :
    MeasurePreserving (fun z : I → Z => (z i, z j)) (Measure.pi μ) ((μ i).prod (μ j)) := by
  let e : Fin 2 → I := ![i, j]
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [e]
  exact (measurePreserving_piFinTwo (fun a => μ (e a))).comp
    (coordinateSelection_family_measurePreserving μ e he)

omit [Fintype J] in
theorem integral_coordinate
    (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)] (i : I)
    {f : Z → ℝ} (hf : AEStronglyMeasurable f (μ i)) :
    (∫ z : I → Z, f (z i) ∂Measure.pi μ) = ∫ z, f z ∂μ i :=
  integral_comp_measurePreserving (coordinate_eval_measurePreserving μ i) hf

omit [Fintype J] in
theorem covariance_distinct_coordinates
    (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)] (i j : I) (hij : i ≠ j)
    {f g : Z → ℝ} (hf : MemLp f 2 (μ i)) (hg : MemLp g 2 (μ j)) :
    covariance (Measure.pi μ) (fun z => f (z i)) (fun z => g (z j)) = 0 := by
  unfold covariance
  rw [integral_comp_measurePreserving (coordinate_pair_measurePreserving μ i j hij)
      (f := fun z : Z × Z => f z.1 * g z.2)
      ((hf.integrable one_le_two).mul_prod (hg.integrable one_le_two)).aestronglyMeasurable,
    integral_prod_mul, integral_coordinate μ i hf.aestronglyMeasurable,
    integral_coordinate μ j hg.aestronglyMeasurable, sub_self]

omit [Fintype J] in
theorem covariance_same_coordinate
    (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)] (i : I)
    {f g : Z → ℝ} (hf : MemLp f 2 (μ i)) (hg : MemLp g 2 (μ i)) :
    covariance (Measure.pi μ) (fun z => f (z i)) (fun z => g (z i)) =
      covariance (μ i) f g :=
  covariance_comp_measurePreserving (coordinate_eval_measurePreserving μ i) hf hg

omit [Fintype J] in
theorem coordinate_iIndepFun
    (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)] :
    iIndepFun (fun i (z : I → Z) => z i) (Measure.pi μ) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  simp only [fun i => (coordinate_eval_measurePreserving μ i).map_eq]
  exact Measure.map_id

omit [Fintype J] in
theorem lintegral_coordinate_product
    (μ : I → Measure Z) [∀ i, IsProbabilityMeasure (μ i)]
    (f : I → Z → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ z : I → Z, ∏ i, f i (z i) ∂Measure.pi μ) = ∏ i, ∫⁻ z, f i z ∂μ i := by
  have hi := (coordinate_iIndepFun μ).comp f hf
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun (i : I) (z : I → Z) => f i (z i)) hi (fun i => (hf i).comp (measurable_pi_apply i))]
  exact Finset.prod_congr rfl (fun i _ =>
    (coordinate_eval_measurePreserving μ i).lintegral_comp (hf i))

end CausalLowerbound.UpperBound

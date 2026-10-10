import Mathlib.MeasureTheory.Constructions.Pi

/-! Separate any distinguished coordinate from a finite product, preserving
the product measure.  This also applies to the remaining coordinates of an
overlapping tuple when the anchor is not among the shared observations. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {I Z : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Z]

def coordinateSplit (a : I) : (I → Z) ≃ᵐ (Z × ({i : I // i ≠ a} → Z)) where
  toFun x := (x a, fun i => x i)
  invFun z i := if hi : i = a then z.1 else z.2 ⟨i, hi⟩
  left_inv := by intro x; funext i; by_cases hi : i = a <;> simp [hi]
  right_inv := by
    intro z
    apply Prod.ext
    · simp
    · funext i; simp [i.property]
  measurable_toFun := (measurable_pi_apply a).prodMk
    (measurable_pi_lambda _ (fun i => measurable_pi_apply (i : I)))
  measurable_invFun := by
    change Measurable (fun z : Z × ({i : I // i ≠ a} → Z) =>
      fun i => if hi : i = a then z.1 else z.2 ⟨i, hi⟩)
    apply measurable_pi_lambda
    intro i
    by_cases hi : i = a
    · simp only [hi, dif_pos rfl]
      exact measurable_fst
    · simp only [dif_neg hi]
      exact (measurable_pi_apply (⟨i, hi⟩ : {i : I // i ≠ a})).comp measurable_snd

omit [Fintype I] in
@[simp] theorem coordinateSplit_fst (a : I) (x : I → Z) : (coordinateSplit a x).1 = x a := rfl

omit [Fintype I] in
@[simp] theorem coordinateSplit_snd (a : I) (x : I → Z) (i : {i : I // i ≠ a}) :
    (coordinateSplit a x).2 i = x i := rfl

theorem coordinateSplit_measurePreserving (μ : Measure Z) [SigmaFinite μ] (a : I) :
    MeasurePreserving (coordinateSplit a) (Measure.pi (fun _ : I => μ))
      (μ.prod (Measure.pi (fun _ : {i : I // i ≠ a} => μ))) := by
  suffices hs : MeasurePreserving (coordinateSplit (Z := Z) a).symm
      (μ.prod (Measure.pi (fun _ : {i : I // i ≠ a} => μ))) (Measure.pi (fun _ : I => μ)) from hs.symm
  refine ⟨(coordinateSplit a).symm.measurable, (Measure.pi_eq ?_).symm⟩
  intro s hs
  rw [Measure.map_apply (coordinateSplit a).symm.measurable (MeasurableSet.univ_pi hs)]
  have he : (coordinateSplit (Z := Z) a).symm ⁻¹' Set.univ.pi s =
      s a ×ˢ Set.univ.pi (fun i : {i : I // i ≠ a} => s i) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      constructor
      · simpa [coordinateSplit] using h a
      · intro i
        simpa [coordinateSplit, i.property] using h i
    · rintro ⟨ha, hr⟩ i
      by_cases hi : i = a
      · subst i
        simpa [coordinateSplit] using ha
      · simpa [coordinateSplit, hi] using hr ⟨i, hi⟩
  rw [he, Measure.prod_prod, Measure.pi_pi]
  letI : Fintype {i : I // i = a} := Subtype.fintype (fun i : I => i = a)
  have hprod := Fintype.prod_subtype_mul_prod_subtype (fun i : I => i = a) (fun i => μ (s i))
  haveI : Subsingleton {i : I // i = a} :=
    ⟨fun x y => Subtype.ext (x.property.trans y.property.symm)⟩
  rw [Fintype.prod_subsingleton _ ⟨a, rfl⟩] at hprod
  exact hprod

theorem coordinateSplit_volume_preserving {W : Type*} [MeasureSpace W]
    [SigmaFinite (volume : Measure W)]
    (a : I) : MeasurePreserving (coordinateSplit (Z := W) a) volume volume :=
  coordinateSplit_measurePreserving volume a

end CausalLowerbound.UpperBound

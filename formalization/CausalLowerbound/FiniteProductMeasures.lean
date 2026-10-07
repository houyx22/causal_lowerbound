import CausalLowerbound.DiscreteTilt
import Mathlib.MeasureTheory.Constructions.Pi

/-! Coordinate marginals and domination of finite product measures. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal NNReal Classical
namespace CausalLowerbound
variable {I K X Y A : Type*} [Fintype I] [Fintype K]
  [MeasurableSpace X] [MeasurableSpace Y]

theorem measurePreserving_coordinateSelection (μ : Measure X) [IsProbabilityMeasure μ]
    (e : I → K) (he : Function.Injective e) :
    MeasurePreserving (fun x : K → X => fun i => x (e i))
      (Measure.pi (fun _ : K => μ)) (Measure.pi (fun _ : I => μ)) := by
  let p : K → Prop := fun k => k ∈ Set.range e
  letI : Fintype (Subtype p) := Subtype.fintype p
  let E : I ≃ Subtype p := Equiv.ofInjective e he
  have hs := measurePreserving_piEquivPiSubtypeProd (fun _ : K => μ) p
  have hf : MeasurePreserving Prod.fst
      ((Measure.pi (fun _ : Subtype p => μ)).prod
        (Measure.pi (fun _ : {k // ¬ p k} => μ)))
      (Measure.pi (fun _ : Subtype p => μ)) := by
    refine ⟨measurable_fst, ?_⟩
    simp
  have hr := measurePreserving_piCongrLeft (fun _ : I => μ) E.symm
  convert hr.comp (hf.comp hs) using 1
  funext x i
  simp [Function.comp_def, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft', MeasurableEquiv.piEquivPiSubtypeProd,
    Equiv.piEquivPiSubtypeProd, E]
  rfl

theorem finiteProduct_mono (μ ν : I → Measure X) (h : ∀ i, μ i ≤ ν i) :
    Measure.pi μ ≤ Measure.pi ν := by
  have ho : OuterMeasure.pi (fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    apply OuterMeasure.le_pi.mpr
    intro s _
    exact (OuterMeasure.pi_pi_le _ s).trans (Finset.prod_le_prod' (fun i _ => h i (s i)))
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.pi, toMeasure_apply _ _ hs]
  exact ho s

theorem finiteProduct_smul (μ : I → Measure X) [∀ i, SigmaFinite (μ i)]
    (c : ℝ≥0) :
    Measure.pi (fun i => c • μ i) = (c ^ Fintype.card I) • Measure.pi μ := by
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

theorem finiteProduct_le_smul (μ ν : I → Measure X) [∀ i, SigmaFinite (ν i)]
    (c : ℝ≥0) (h : ∀ i, μ i ≤ c • ν i) :
    Measure.pi μ ≤ (c ^ Fintype.card I) • Measure.pi ν := by
  rw [← finiteProduct_smul]
  exact finiteProduct_mono μ (fun i => c • ν i) h

namespace DiscreteLaw

theorem mixMeasures_map (μ : DiscreteLaw A) (M : A → Measure X)
    (f : X → Y) (hf : Measurable f) :
    (μ.mixMeasures M).map f = μ.mixMeasures (fun a => (M a).map f) := by
  simp only [mixMeasures, Measure.map_sum hf.aemeasurable, Measure.map_smul]

theorem mixMeasures_le (μ : DiscreteLaw A) (M : A → Measure X) (ν : Measure X)
    (h : ∀ a, M a ≤ ν) : μ.mixMeasures M ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [mixMeasures, Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    (∑' a, ENNReal.ofReal (μ.weight a) * M a s) ≤
        ∑' a, ENNReal.ofReal (μ.weight a) * ν s :=
      ENNReal.tsum_le_tsum (fun a => mul_le_mul_left' (h a s) _)
    _ = ν s := by
      rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg μ.nonneg μ.summable_weight,
        μ.tsum_weight, ENNReal.ofReal_one, one_mul]

end DiscreteLaw
end CausalLowerbound

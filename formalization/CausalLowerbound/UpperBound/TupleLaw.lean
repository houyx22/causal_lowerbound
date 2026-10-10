import CausalLowerbound.UpperBound.ConditionalScore
import CausalLowerbound.UpperBound.KernelPi

/-! Conditional product laws agree with the original iid observation law.
This is an identity of measures, so it applies to every integrable empirical
kernel, including weights that depend on the entire covariate tuple. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Classical

namespace CausalLowerbound.UpperBound

variable {I X Z : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSpace Z]

def coordinateProductKernel (κ : Kernel X Z) [IsMarkovKernel κ] :
    Kernel (I → X) (I → Z) :=
  finiteProductKernel (fun i : I => κ.comap (fun x => x i) (measurable_pi_apply i))

instance coordinateProductKernel_markov (κ : Kernel X Z) [IsMarkovKernel κ] :
    IsMarkovKernel (coordinateProductKernel (I := I) κ) := by
  unfold coordinateProductKernel
  infer_instance

theorem coordinateProductKernel_apply (κ : Kernel X Z) [IsMarkovKernel κ] (x : I → X) :
    coordinateProductKernel κ x = Measure.pi (fun i => κ (x i)) := by
  rw [coordinateProductKernel, finiteProductKernel_apply]
  rfl

theorem tuple_pairing_measurePreserving (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel X Z) [IsMarkovKernel κ] :
    MeasurePreserving (fun z : (I → X) × (I → Z) => fun i => (z.1 i, z.2 i))
      ((Measure.pi (fun _ : I => μ)) ⊗ₘ coordinateProductKernel κ)
      (Measure.pi (fun _ : I => μ ⊗ₘ κ)) := by
  have hm : Measurable (fun z : (I → X) × (I → Z) => fun i => (z.1 i, z.2 i)) := by
    fun_prop
  refine ⟨hm, (Measure.pi_eq ?_).symm⟩
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs),
    Measure.compProd_apply ((MeasurableSet.univ_pi hs).preimage hm)]
  have hsection (x : I → X) :
      Prod.mk x ⁻¹' ((fun z : (I → X) × (I → Z) => fun i => (z.1 i, z.2 i)) ⁻¹'
        Set.univ.pi s) = Set.univ.pi (fun i => Prod.mk (x i) ⁻¹' s i) := rfl
  simp_rw [hsection, coordinateProductKernel_apply, Measure.pi_pi]
  rw [lintegral_coordinate_product (fun _ : I => μ)
    (fun i x => κ x (Prod.mk x ⁻¹' s i))
    (fun i => Kernel.measurable_kernel_prodMk_left (hs i))]
  exact Finset.prod_congr rfl (fun i _ => (Measure.compProd_apply (hs i)).symm)

namespace RealOutcomeModel

variable {d : Type*} [Fintype d] {ε lower upper M₂ : ℝ}
variable (M : RealOutcomeModel d ε lower upper M₂)

def conditionalTupleKernel (I : Type*) [Fintype I] :
    Kernel (I → d → ℝ) (I → Bool × ℝ) := coordinateProductKernel M.conditional

instance conditionalTupleKernel_markov (I : Type*) [Fintype I] :
    IsMarkovKernel (M.conditionalTupleKernel I) := by
  unfold conditionalTupleKernel
  infer_instance

theorem conditionalTupleKernel_apply (X : I → d → ℝ) :
    M.conditionalTupleKernel I X = M.conditionalTupleLaw X :=
  coordinateProductKernel_apply M.conditional X

theorem tupleLaw_measurePreserving :
    MeasurePreserving
      (fun z : (I → d → ℝ) × (I → Bool × ℝ) => fun i => (z.1 i, z.2 i))
      ((Measure.pi (fun _ : I => M.design)) ⊗ₘ M.conditionalTupleKernel I)
      (M.sampleLaw I) :=
  tuple_pairing_measurePreserving M.design M.conditional

theorem integral_sampleLaw_via_conditional {F : (I → (d → ℝ) × (Bool × ℝ)) → ℝ}
    (hF : Integrable F (M.sampleLaw I)) :
    (∫ z, F z ∂M.sampleLaw I) =
      ∫ X, ∫ z, F (fun i => (X i, z i)) ∂M.conditionalTupleLaw X
        ∂Measure.pi (fun _ : I => M.design) := by
  have hmp := M.tupleLaw_measurePreserving (I := I)
  have hi : Integrable
      (fun z : (I → d → ℝ) × (I → Bool × ℝ) => F (fun i => (z.1 i, z.2 i)))
      ((Measure.pi (fun _ : I => M.design)) ⊗ₘ M.conditionalTupleKernel I) :=
    (hmp.integrable_comp hF.aestronglyMeasurable).mpr hF
  rw [← integral_comp_measurePreserving hmp hF.aestronglyMeasurable,
    Measure.integral_compProd hi]
  simp only [conditionalTupleKernel_apply]

end RealOutcomeModel
end CausalLowerbound.UpperBound

import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fintype.Option

/-! Finite products of Markov kernels with a common parameter.  The result
is constructed from binary products and measurable coordinate equivalences. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Classical

namespace CausalLowerbound.UpperBound

universe u v w
variable {Ω : Type v} {Z : Type w} [MeasurableSpace Ω] [MeasurableSpace Z]

theorem exists_finiteProductKernel (I : Type u) [Fintype I]
    (κ : I → Kernel Ω Z) [∀ i, IsMarkovKernel (κ i)] :
    ∃ η : Kernel Ω (I → Z), ∀ x, η x = Measure.pi (fun i => κ i x) := by
  have hall : ∀ (J : Type u) [Fintype J], ∀ κ : J → Kernel Ω Z,
      (∀ j, IsMarkovKernel (κ j)) →
      ∃ η : Kernel Ω (J → Z), ∀ x, η x = Measure.pi (fun j => κ j x) := by
    intro J instJ
    refine Fintype.induction_empty_option (P := fun J _ => ∀ κ : J → Kernel Ω Z,
      (∀ j, IsMarkovKernel (κ j)) →
      ∃ η : Kernel Ω (J → Z), ∀ x, η x = Measure.pi (fun j => κ j x)) ?_ ?_ ?_ J
    · intro J K instK e ih κ hκ
      letI : Fintype J := Fintype.ofEquiv K e.symm
      obtain ⟨η, hη⟩ := ih (fun j => κ (e j)) (fun j => hκ (e j))
      refine ⟨η.map (MeasurableEquiv.piCongrLeft (fun _ : K => Z) e), ?_⟩
      intro x
      rw [Kernel.map_apply _ (MeasurableEquiv.piCongrLeft (fun _ : K => Z) e).measurable,
        hη x]
      exact Measure.pi_map_piCongrLeft (β := fun _ : K => Z) (μ := fun j => κ j x) e
    · intro κ _
      refine ⟨Kernel.deterministic (fun _ : Ω => fun i : PEmpty => nomatch i) measurable_const, ?_⟩
      intro x
      rw [Kernel.deterministic_apply, Measure.pi_of_empty]
      congr 1
      funext i
      exact i.elim
    · intro J instJ ih κ hκ
      letI : ∀ j, IsMarkovKernel (κ j) := hκ
      obtain ⟨η, hη⟩ := ih (fun j => κ (some j)) (fun j => hκ (some j))
      letI : IsMarkovKernel η := ⟨fun x => by rw [hη x]; infer_instance⟩
      refine ⟨(η ×ₖ κ none).map (MeasurableEquiv.piOptionEquivProd (fun _ => Z)).symm, ?_⟩
      intro x
      rw [Kernel.map_apply _ (MeasurableEquiv.piOptionEquivProd (fun _ => Z)).symm.measurable,
        Kernel.prod_apply, hη x]
      exact Measure.pi_map_piOptionEquivProd (fun i => κ i x)
  exact hall I κ (fun _ => inferInstance)

def finiteProductKernel {I : Type u} [Fintype I]
    (κ : I → Kernel Ω Z) [∀ i, IsMarkovKernel (κ i)] : Kernel Ω (I → Z) :=
  (exists_finiteProductKernel I κ).choose

theorem finiteProductKernel_apply {I : Type u} [Fintype I]
    (κ : I → Kernel Ω Z) [∀ i, IsMarkovKernel (κ i)] (x : Ω) :
    finiteProductKernel κ x = Measure.pi (fun i => κ i x) :=
  (exists_finiteProductKernel I κ).choose_spec x

instance finiteProductKernel_markov {I : Type u} [Fintype I]
    (κ : I → Kernel Ω Z) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (finiteProductKernel κ) :=
  ⟨fun x => by rw [finiteProductKernel_apply]; infer_instance⟩

end CausalLowerbound.UpperBound

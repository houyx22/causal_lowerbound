import CausalLowerbound.PartB.PhysicalDesign
import Mathlib.MeasureTheory.Constructions.Pi

/-! Completing a retained configuration with independent unit-cube
ghosts. The completion lies in the full closed chart almost everywhere,
including when either coordinate set is empty. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {X I K G d : Type*} [Fintype I] [Fintype K] [Fintype G] [Fintype d]

def completedSites (e : K ⊕ G ≃ I) (u : K → X) (z : G → X) : I → X :=
  Sum.elim u z ∘ e.symm

def completedConfiguration (e : K ⊕ G ≃ I) (u : K → d → ℝ) (z : G → d → ℝ) : I × d → ℝ :=
  fun p => completedSites e u z p.1 p.2

@[simp] theorem completedSites_retained (e : K ⊕ G ≃ I) (u : K → X) (z : G → X) (i : K) :
    completedSites e u z (e (Sum.inl i)) = u i := by
  simp only [completedSites, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem completedSites_ghost (e : K ⊕ G ≃ I) (u : K → X) (z : G → X) (i : G) :
    completedSites e u z (e (Sum.inr i)) = z i := by
  simp only [completedSites, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]

theorem completedConfiguration_mem_Icc (e : K ⊕ G ≃ I) (u : K → d → ℝ) (z : G → d → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) (hz : ∀ j, z j ∈ Set.Icc (0 : d → ℝ) 1) :
    completedConfiguration e u z ∈ Set.Icc (0 : I × d → ℝ) 1 := by
  have hh (i : I) : completedSites e u z i ∈ Set.Icc (0 : d → ℝ) 1 := by
    cases he : e.symm i with
    | inl j => simpa only [completedSites, Function.comp_apply, he, Sum.elim_inl] using hu j
    | inr j => simpa only [completedSites, Function.comp_apply, he, Sum.elim_inr] using hz j
  exact ⟨fun p => (hh p.1).1 p.2, fun p => (hh p.1).2 p.2⟩

theorem ae_cubeSites :
    ∀ᵐ z : G → d → ℝ ∂Measure.pi (fun _ : G => cubeMeasure d),
      ∀ j, z j ∈ Set.Icc (0 : d → ℝ) 1 := by
  apply Filter.eventually_all.mpr
  intro j
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : G => cubeMeasure d) (i := j)).eventually
    (ae_restrict_mem measurableSet_Icc)

theorem ae_completedConfiguration_mem_Icc (e : K ⊕ G ≃ I) (u : K → d → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) :
    ∀ᵐ z : G → d → ℝ ∂Measure.pi (fun _ : G => cubeMeasure d),
      completedConfiguration e u z ∈ Set.Icc (0 : I × d → ℝ) 1 := by
  filter_upwards [ae_cubeSites (G := G) (d := d)] with z hz
  exact completedConfiguration_mem_Icc e u z hu hz

theorem integral_completedConfiguration_congr (e : K ⊕ G ≃ I) (u : K → d → ℝ)
    (hu : ∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) (f g : (I × d → ℝ) → ℝ)
    (hfg : ∀ v ∈ Set.Icc (0 : I × d → ℝ) 1, f v = g v) :
    (∫ z : G → d → ℝ, f (completedConfiguration e u z) ∂Measure.pi (fun _ : G => cubeMeasure d)) =
      ∫ z : G → d → ℝ, g (completedConfiguration e u z) ∂Measure.pi (fun _ : G => cubeMeasure d) := by
  apply integral_congr_ae
  filter_upwards [ae_completedConfiguration_mem_Icc e u hu] with z hz
  exact hfg _ hz

end CausalLowerbound.PartC

import CausalLowerbound.PartC.UnitCubeGhosts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Normed.Group.Bounded

/-! Continuous ghost functions are integrable on the actual finite
product of unit cubes. Compactness supplies the bound required for
integrability, independently of the later quantitative error estimates. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {K G d : Type*} [Fintype K] [Fintype G] [Fintype d]

theorem continuous_integrable_cubeSites (f : (G → d → ℝ) → ℝ) (hf : Continuous f) :
    Integrable f (Measure.pi (fun _ : G => cubeMeasure d)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : G → d → ℝ) 1)).exists_bound_of_continuousOn hf.continuousOn
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  filter_upwards [ae_cubeSites (G := G) (d := d)] with g hg
  exact hC g ⟨fun j => (hg j).1, fun j => (hg j).2⟩

theorem continuous_integrable_cubeBlocks (G : K → Type*) [∀ k, Fintype (G k)]
    (f : (∀ k, G k → d → ℝ) → ℝ) (hf : Continuous f) :
    Integrable f (Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))) := by
  let μ := fun k => Measure.pi (fun _ : G k => cubeMeasure d)
  have hae : ∀ᵐ g : ∀ k, G k → d → ℝ ∂Measure.pi μ,
      ∀ k j, g k j ∈ Set.Icc (0 : d → ℝ) 1 := by
    apply Filter.eventually_all.mpr
    intro k
    exact (Measure.tendsto_eval_ae_ae (μ := μ) (i := k)).eventually (ae_cubeSites (G := G k) (d := d))
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ∀ k, G k → d → ℝ) 1)).exists_bound_of_continuousOn hf.continuousOn
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  filter_upwards [hae] with g hg
  exact hC g ⟨fun k j => (hg k j).1, fun k j => (hg k j).2⟩

end CausalLowerbound.PartC

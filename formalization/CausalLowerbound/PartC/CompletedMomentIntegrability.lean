import CausalLowerbound.PartC.DensityCarrierMarginals
import CausalLowerbound.PartC.GhostSignResampling

/-! Integrability of genuine density-weighted coefficient moments after
retained/ghost completion. Closed-chart HasSum identities transfer this
integrability to their represented functions, without assuming continuity
of a singular interpolation formula. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {X d V I G : Type*} [Fintype d] [Fintype V] [Fintype I] [Fintype G]

theorem weightedCarrierMarginal_abs_le (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ)
    (g : ℕ → ℝ) (B M : ℝ) (hB : 0 ≤ B) (hb : ∀ n x, |density n x| ≤ B)
    (hg : ∀ n, |g n| ≤ M) (u : V → X) :
    |weightedCarrierMarginal H density g u| ≤ B ^ Fintype.card V * M := by
  apply H.abs_expect_le
  intro n
  rw [abs_mul]
  exact mul_le_mul (carrierTensor_abs_le density B hb n u) (hg n)
    (abs_nonneg _) (pow_nonneg hB _)

theorem weightedCarrierMarginal_completed_integrable
    (H : DiscreteLaw ℕ) (density : ℕ → (d → ℝ) → ℝ) (g : ℕ → ℝ)
    (B M : ℝ) (hB : 0 ≤ B) (hc : ∀ n, Continuous (density n))
    (hb : ∀ n x, |density n x| ≤ B) (hg : ∀ n, |g n| ≤ M)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) :
    Integrable (fun z : G → d → ℝ => weightedCarrierMarginal H density g (completedSites e u z))
      (Measure.pi (fun _ : G => cubeMeasure d)) := by
  have hcoord : Continuous (fun z : G → d → ℝ => completedSites e u z) :=
    continuous_pi (fun v => completedSites_ghost_continuous e u v)
  have hf := (weightedCarrierMarginal_continuous H density g B M hB hc hb hg).comp hcoord
  apply (integrable_const (B ^ Fintype.card V * M)).mono' hf.aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs] using weightedCarrierMarginal_abs_le H density g B M hB hb hg (completedSites e u z)

theorem completed_integrable_of_hasSum
    (H : DiscreteLaw ℕ) (density : ℕ → (d → ℝ) → ℝ) (g : ℕ → ℝ)
    (B M : ℝ) (hB : 0 ≤ B) (hc : ∀ n, Continuous (density n))
    (hb : ∀ n x, |density n x| ≤ B) (hg : ∀ n, |g n| ≤ M)
    (F : (V × d → ℝ) → ℝ)
    (hsum : ∀ v : UnitChart (V × d), HasSum (fun n => (H.weight n * g n) *
      ∏ j, density n (fun a => v.val (j, a))) (F v.val))
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (hu : ∀ i, u i ∈ Set.Icc (0 : d → ℝ) 1) :
    Integrable (fun z : G → d → ℝ => F (completedConfiguration e u z))
      (Measure.pi (fun _ : G => cubeMeasure d)) := by
  apply (weightedCarrierMarginal_completed_integrable H density g B M hB hc hb hg e u).congr
  filter_upwards [ae_completedConfiguration_mem_Icc e u hu] with z hz
  exact weightedCarrierMarginal_eq_of_hasSum H density g (completedSites e u z) _
    (hsum ⟨completedConfiguration e u z, hz⟩)

end CausalLowerbound.PartC

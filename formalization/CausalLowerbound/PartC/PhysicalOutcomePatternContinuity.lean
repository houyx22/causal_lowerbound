import CausalLowerbound.PartC.OutcomePatternContinuity
import CausalLowerbound.PartC.PhysicalOutcomePatternBounds
import CausalLowerbound.PartC.WeightedOutcomeStability
import CausalLowerbound.PartC.CubeGhostIntegrability

/-! Normalized cubic patterns on completed physical configurations.
The retained formal values remain fixed while the ghost variables vary. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative PartB PartB.ShellGeometry
variable {d V I G : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]
  [Fintype I] [Fintype G]

def partialPhysicalOutcomePatternWeight (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ)
    (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (f : Degree V 3) (g : G → d → ℝ) : ℝ :=
  weightedOutcomePatternWeight N
    (fun v => normalizedRoughVariance x₀ r h k c w N (configurationSite (completedConfiguration e u g) v))
    B (completedConfiguration e u g)
    (completedSites e a (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (g j))) ζ f

theorem partialPhysicalOutcomePatternWeight_continuous (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (hc : 0 < c) (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (f : Degree V 3) :
    Continuous (partialPhysicalOutcomePatternWeight x₀ ℓ r h k c w N B e u a ζ f) := by
  have hcoord : Continuous (fun g : G → d → ℝ => completedConfiguration e u g) :=
    continuous_pi (fun v => (continuous_apply v.2).comp (completedSites_ghost_continuous e u v.1))
  have hκ (v : V) : Continuous (fun g : G → d → ℝ =>
      normalizedRoughVariance x₀ r h k c w N (configurationSite (completedConfiguration e u g) v)) :=
    (normalizedRoughVariance_continuous x₀ r h k c w N hc).comp
      (completedSites_ghost_continuous e u v)
  have hz (v : V) : Continuous (fun g : G → d → ℝ =>
      completedSites e a (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (g j)) v) :=
    (completedSites_ghost_continuous e a v).comp (continuous_pi (fun j =>
      (normalizedRoughChart_continuous x₀ ℓ r h k c w N hc ζ).comp (continuous_apply j)))
  exact continuous_const.mul (continuous_outcomePatternWeight _ hκ B _ hcoord _ hz ζ f)

theorem partialPhysicalOutcomePatternWeight_bound (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (C : ℝ) (hC : 1 ≤ C) (hCz : N₀ / c ≤ C) (hCκ : 1 / N₀ ^ 2 ≤ C)
    (hNa : ∀ i, |N * a i| ≤ C) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (f : Degree V 3) (g : G → d → ℝ) :
    |partialPhysicalOutcomePatternWeight x₀ ℓ r h k c w N B e u a ζ f g| ≤
      (C ^ 4) ^ Fintype.card V * ‖B‖ := by
  apply weightedOutcomePatternWeight_bound N _ B _ _ ζ f C hC
  · intro v
    cases hv : e.symm v with
    | inl i => simpa only [completedSites, Function.comp_apply, hv, Sum.elim_inl] using ha i
    | inr i => simpa only [completedSites, Function.comp_apply, hv, Sum.elim_inr] using
        normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (g i)
  · intro v
    cases hv : e.symm v with
    | inl i => simpa only [completedSites, Function.comp_apply, hv, Sum.elim_inl] using hNa i
    | inr i => simpa only [completedSites, Function.comp_apply, hv, Sum.elim_inr] using
        (normalizedRoughChart_scaled_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (g i)).trans hCz
  · intro i
    exact (normalizedRoughVariance_bound x₀ r h k c w N N₀ hc hN₀ hN hm _).trans hCκ

theorem partialPhysicalOutcomePatternWeight_integrable (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (hc : 0 < c) (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (f : Degree V 3) :
    Integrable (partialPhysicalOutcomePatternWeight x₀ ℓ r h k c w N B e u a ζ f)
      (Measure.pi (fun _ : G => cubeMeasure d)) :=
  continuous_integrable_cubeSites _
    (partialPhysicalOutcomePatternWeight_continuous x₀ ℓ r h k c w N hc B e u a ζ f)

end CausalLowerbound.PartC

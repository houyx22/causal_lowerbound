import CausalLowerbound.PartC.WeightedPropensityStability
import CausalLowerbound.PartC.PhysicalPatternBounds
import CausalLowerbound.PartC.GhostSignResampling

/-! The selected-slot weights on actual completed physical charts are
continuous and uniformly bounded, including arbitrary fixed retained
formal variables. The correction is the physical propensity correction. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative PartB PartB.ShellGeometry
variable {d V J I G : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype I] [Fintype G]

theorem continuous_weightedPropensityPatternWeight {X : Type*} [TopologicalSpace X]
    (N : ℝ) (κ : X → V → ℝ) (hκ : ∀ i, Continuous (fun x => κ x i))
    (W : Array d V J 1) (u : X → V × d → ℝ) (hu : Continuous u)
    (z : X → V → ℝ) (hz : ∀ i, Continuous (fun x => z x i))
    (ζ : J → Bool) (S : Finset V) :
    Continuous (fun x => weightedPropensityPatternWeight N (κ x) W (u x) (z x) ζ S) := by
  apply continuous_const.mul
  apply continuous_finset_sum
  intro r _
  have hc : Continuous (fun x => (toContinuous (W r) (torusProjection (u x))).re) :=
    Complex.continuous_re.comp ((toContinuous (W r)).continuous.comp
      (torusProjection_quotient.continuous.comp hu))
  apply (continuous_const.mul hc).mul
  apply continuous_finset_prod
  intro i _
  by_cases hi : i ∈ S
  · by_cases ha : r.1 i = 0
    · simpa only [propensitySlotFactor, if_pos hi, if_pos ha] using hz i
    · simpa only [propensitySlotFactor, if_pos hi, if_neg ha] using hκ i
  · simpa only [propensitySlotFactor, if_neg hi] using (hz i).pow (r.1 i).val

theorem physicalPropensitySlotCorrection_continuous (x₀ : d → ℝ) (r h : ℝ) (k : d → ℤ)
    (c w N ja : ℝ) (hc : 0 < c) (i : V) :
    Continuous (fun u : V × d → ℝ => physicalPropensitySlotCorrection x₀ r h k c w N ja u i) := by
  have hcoord : Continuous (fun u : V × d → ℝ => fun j => 4 * u (i, j) - 2) := by fun_prop
  have hpoint : Continuous (fun u : V × d → ℝ => fun j => x₀ j + r * (k j + 4 * u (i, j) - 2)) := by fun_prop
  have hm := (assignmentMultiplier_smooth c w hc).continuous.comp hcoord
  have hG := (rescaled_smooth _ quadraticPartition_smooth x₀ h).continuous.comp hpoint
  exact (((hm.div_const N).pow 2).mul continuous_const).mul (hG.pow 4)

def partialPhysicalPatternWeight (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N ja : ℝ)
    (B : Array d V (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (S : Finset V) (g : G → d → ℝ) : ℝ :=
  weightedPropensityPatternWeight N
    (physicalPropensitySlotCorrection x₀ r h k c w N ja (completedConfiguration e u g))
    B (completedConfiguration e u g)
    (completedSites e a (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (g j))) ζ S

theorem partialPhysicalPatternWeight_continuous (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N ja : ℝ) (hc : 0 < c) (B : Array d V (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (S : Finset V) :
    Continuous (partialPhysicalPatternWeight x₀ ℓ r h k c w N ja B e u a ζ S) := by
  have hcoord : Continuous (fun g : G → d → ℝ => completedConfiguration e u g) :=
    continuous_pi (fun p => (continuous_apply p.2).comp (completedSites_ghost_continuous e u p.1))
  have hz (v : V) : Continuous (fun g : G → d → ℝ =>
      completedSites e a (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (g j)) v) :=
    (completedSites_ghost_continuous e a v).comp (continuous_pi (fun j =>
      (normalizedRoughChart_continuous x₀ ℓ r h k c w N hc ζ).comp (continuous_apply j)))
  exact continuous_weightedPropensityPatternWeight N _
    (fun i => (physicalPropensitySlotCorrection_continuous x₀ r h k c w N ja hc i).comp hcoord)
    B _ hcoord _ hz ζ S

theorem partialPhysicalPatternWeight_bound (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ ja : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hja : ja ^ 2 ≤ 1)
    (B : Array d V (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (C : ℝ) (hC : 1 ≤ C) (hCz : N₀ / c ≤ C) (hCκ : 1 / (c * N₀) ≤ C)
    (hNa : ∀ i, |N * a i| ≤ C) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (S : Finset V) (g : G → d → ℝ) :
    |partialPhysicalPatternWeight x₀ ℓ r h k c w N ja B e u a ζ S g| ≤
      C ^ Fintype.card V * ‖B‖ := by
  apply weightedPropensityPatternWeight_bound N _ B _ _ ζ S C hC
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
    exact (physicalPropensityCorrection_scaled_bound x₀ r h k c w N N₀ ja hc hN₀ hN hm hja _ i).trans hCκ

end CausalLowerbound.PartC

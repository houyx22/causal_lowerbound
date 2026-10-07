import CausalLowerbound.PartC.OutcomePolynomialTarget
import CausalLowerbound.PartC.NormalizedRoughMoments
import CausalLowerbound.PartC.GhostSignResampling
import CausalLowerbound.PartC.BlockPolynomialFunctional

/-! Continuity of cubic pattern weights and polynomial functionals on
completed physical charts. Retained formal values are fixed while all
ghost positions and their actual rough-field values vary. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative PartB PartB.ShellGeometry MvPolynomial
variable {d V J I G : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype I] [Fintype G]

theorem continuous_outcomePatternWeight {X : Type*} [TopologicalSpace X]
    (κ : X → V → ℝ) (hκ : ∀ i, Continuous (fun x => κ x i))
    (W : Array d V J 3) (u : X → V × d → ℝ) (hu : Continuous u)
    (z : X → V → ℝ) (hz : ∀ i, Continuous (fun x => z x i))
    (ζ : J → Bool) (f : Degree V 3) :
    Continuous (fun x => outcomePatternWeight (κ x) W (u x) (z x) ζ f) := by
  apply continuous_finset_sum
  intro r _
  have hc : Continuous (fun x => (toContinuous (W r) (torusProjection (u x))).re) :=
    Complex.continuous_re.comp ((toContinuous (W r)).continuous.comp
      (torusProjection_quotient.continuous.comp hu))
  apply (continuous_const.mul hc).mul
  apply continuous_finset_prod
  intro i _
  by_cases hf : f i = 0
  · simpa only [outcomeSlotFactor, if_pos hf] using (hz i).pow (r.1 i).val
  · have hm : Continuous (fun x => Representative.outcomeMoment (κ x i) (r.1 i)) := by
      unfold Representative.outcomeMoment
      split_ifs
      · exact continuous_const
      · exact hκ i
      · exact continuous_const
    simpa only [outcomeSlotFactor, if_neg hf] using hm.mul ((hz i).pow (f i).val)

theorem continuous_cubicSiteFunctional {X : Type*} [TopologicalSpace X]
    (w : X → Degree V 3 → ℝ) (hw : ∀ f, Continuous (fun x => w x f))
    (p : MvPolynomial V ℝ) : Continuous (fun x => cubicSiteFunctional (w x) p) := by
  change Continuous (fun x => ∑ m ∈ p.support, p.coeff m *
    (if hm : ∀ v, m v ≤ 3 then w x (cubicSiteDegree m hm) else 0))
  apply continuous_finset_sum
  intro m _
  apply continuous_const.mul
  by_cases hm : ∀ v, m v ≤ 3
  · simpa only [dif_pos hm] using hw (cubicSiteDegree m hm)
  · simpa only [dif_neg hm] using (continuous_const : Continuous (fun _ : X => (0 : ℝ)))

theorem continuous_blockPolynomialFunctional {X K A : Type*} [TopologicalSpace X]
    [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A]
    (L : X → K → MvPolynomial A ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ k p, Continuous (fun x => L x k p)) (p : MvPolynomial (K × A) ℝ) :
    Continuous (fun x => blockPolynomialFunctional (L x) p) := by
  simp only [blockPolynomialFunctional_expansion]
  apply continuous_finset_sum
  intro m _
  apply continuous_const.mul
  apply continuous_finset_prod
  intro k _
  exact hL k (blockMonomial m k)

theorem normalizedRoughVariance_continuous (x₀ : d → ℝ) (r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (hc : 0 < c) : Continuous (normalizedRoughVariance x₀ r h k c w N) := by
  have hcoord : Continuous (fun u : d → ℝ => fun j => 4 * u j - 2) := by fun_prop
  have hm := (assignmentMultiplier_smooth c w hc).continuous.comp hcoord
  have hG := (rescaled_smooth _ quadraticPartition_smooth x₀ h).continuous.comp
    (roughChartPoint_continuous x₀ r k)
  exact ((hm.div_const N).pow 2).mul (hG.pow 2)

def partialPhysicalOutcomeFunctional (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ)
    (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (g : G → d → ℝ) : MvPolynomial V ℝ →ₗ[ℝ] ℝ :=
  outcomePolynomialFunctional
    (fun v => normalizedRoughVariance x₀ r h k c w N (configurationSite (completedConfiguration e u g) v))
    B (completedConfiguration e u g)
    (completedSites e a (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (g j))) ζ

theorem partialPhysicalOutcomeFunctional_continuous (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (hc : 0 < c) (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (p : MvPolynomial V ℝ) :
    Continuous (fun g => partialPhysicalOutcomeFunctional x₀ ℓ r h k c w N B e u a ζ g p) := by
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
  exact continuous_cubicSiteFunctional _
    (fun f => continuous_outcomePatternWeight _ hκ B _ hcoord _ hz ζ f) p

end CausalLowerbound.PartC

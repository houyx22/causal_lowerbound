import CausalLowerbound.PartC.OutcomePatternIntegration

/-! Diagonal identification of the normalized cubic integrand with
the actual completed physical configuration. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype G]

theorem partialPhysicalOutcomePatternWeight_diagonal (Q : ℕ)
    (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (f : Degree (Fin Q) 3) (g : G → d → ℝ) :
    partialPhysicalOutcomePatternWeight x₀ ℓ r h k c w N B e u
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i)) ζ f g =
      weightedOutcomePatternWeight N
        (fun v => normalizedRoughVariance x₀ r h k c w N (configurationSite (completedConfiguration e u g) v))
        B (completedConfiguration e u g)
        (fun v => normalizedRoughChart x₀ ℓ r h k c w N ζ
          (configurationSite (completedConfiguration e u g) v)) ζ f := by
  have hz : completedSites e (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i))
      (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (g j)) =
      fun v => normalizedRoughChart x₀ ℓ r h k c w N ζ
        (configurationSite (completedConfiguration e u g) v) := by
    funext v
    change completedSites e (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i))
      (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (g j)) v =
        normalizedRoughChart x₀ ℓ r h k c w N ζ (completedSites e u g v)
    cases hv : e.symm v <;> simp only [completedSites, Function.comp_apply, hv,
      Sum.elim_inl, Sum.elim_inr]
  simp only [partialPhysicalOutcomePatternWeight, hz]

theorem normalizedPhysicalOutcomeCubicFunctional_diagonal (Q : ℕ)
    (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N τ : ℝ)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (g : G → d → ℝ) :
    normalizedPhysicalOutcomeCubicFunctional Q x₀ ℓ r h k c w N τ B e u
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i)) ζ g =
      cubicSiteFunctional (fun f => N ^ degreeSize f *
        taperedCubicWeight (completeTaper Q τ (completedConfiguration e u g))
          (outcomePatternWeight
            (fun v => normalizedRoughVariance x₀ r h k c w N (configurationSite (completedConfiguration e u g) v))
            B (completedConfiguration e u g)
            (fun v => normalizedRoughChart x₀ ℓ r h k c w N ζ
              (configurationSite (completedConfiguration e u g) v)) ζ) f) := by
  unfold normalizedPhysicalOutcomeCubicFunctional
  congr 1
  funext f
  rw [weighted_taperedCubicWeight, partialPhysicalOutcomePatternWeight_diagonal]
  by_cases hf : f = 0
  · simp only [selectedOutcomeGhostTaper, if_pos hf, weightedOutcomePatternWeight]
  · simp only [selectedOutcomeGhostTaper, if_neg hf, completedCubeTaper, weightedOutcomePatternWeight]

end CausalLowerbound.PartC

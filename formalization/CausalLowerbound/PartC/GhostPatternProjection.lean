import CausalLowerbound.PartC.PhysicalGhostPatterns
import CausalLowerbound.PartC.TaperedSiteFunctional

/-! Identify the diagonal physical ghost weights with the tapered pattern
integrals in the observation expansion, and combine all independent ghost
coordinates before applying the shared-sign estimates. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G K : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype G] [Fintype K]

theorem physicalGhostPatternWeight_eq_integral (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N ja τ : ℝ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (S : Finset (Fin Q)) :
    physicalGhostPatternWeight Q x₀ ℓ r h k c w N ja τ B e u ζ ζ S =
      ∫ g : G → d → ℝ,
        N ^ S.card * taperedPatternWeight (completeTaper Q τ (completedConfiguration e u g))
          (propensityPatternWeight
            (physicalPropensitySlotCorrection x₀ r h k c w N ja (completedConfiguration e u g))
            B (completedConfiguration e u g)
            (fun v => normalizedRoughChart x₀ ℓ r h k c w N ζ
              (configurationSite (completedConfiguration e u g) v)) ζ) S
        ∂Measure.pi (fun _ : G => cubeMeasure d) := by
  unfold physicalGhostPatternWeight ghostPatternIntegral
  apply integral_congr_ae
  filter_upwards [] with g
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
  simp only [partialPhysicalPatternWeight, hz, weightedPropensityPatternWeight,
    selectedGhostTaper, completedCubeTaper, taperedPatternWeight]
  by_cases hS : S = ∅
  · subst S
    simp
  · simp only [if_neg hS]
    ring

theorem physicalGhostPatternWeight_product_projection
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : K → d → ℤ) (c w N ja τ : ℝ)
    (B : K → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (I G : K → Type*) [∀ a, Fintype (I a)] [∀ a, Fintype (G a)]
    (e : ∀ a, I a ⊕ G a ≃ Fin Q) (u : ∀ a, I a → d → ℝ)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (S : K → Finset (Fin Q)) :
    (∫ g : ∀ a, G a → d → ℝ,
      ∏ a, selectedGhostTaper Q (e a) τ (u a) (S a) (g a) *
        partialPhysicalPatternWeight x₀ ℓ r h (k a) c w N ja (B a) (e a) (u a)
          (fun i => normalizedRoughChart x₀ ℓ r h (k a) c w N ζ (u a i)) η (S a) (g a)
      ∂Measure.pi (fun a => Measure.pi (fun _ : G a => cubeMeasure d))) =
      ∏ a, physicalGhostPatternWeight Q x₀ ℓ r h (k a) c w N ja τ (B a) (e a) (u a) ζ η (S a) := by
  let F := fun a (g : G a → d → ℝ) => selectedGhostTaper Q (e a) τ (u a) (S a) g *
    partialPhysicalPatternWeight x₀ ℓ r h (k a) c w N ja (B a) (e a) (u a)
      (fun i => normalizedRoughChart x₀ ℓ r h (k a) c w N ζ (u a i)) η (S a) g
  have he := @integral_fintype_prod_eq_prod ℝ inferInstance K inferInstance (fun a => G a → d → ℝ) F
    (fun a => ⟨Measure.pi (fun _ : G a => cubeMeasure d)⟩)
    (fun a => inferInstanceAs (SigmaFinite (Measure.pi (fun _ : G a => cubeMeasure d))))
  exact he

end CausalLowerbound.PartC

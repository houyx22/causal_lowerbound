import CausalLowerbound.UpperBound.AcceptedVolume
import CausalLowerbound.UpperBound.RealOutcomeModel
import CausalLowerbound.FiniteProductMeasures

/-! Acceptance probability under a merely measurable bounded design density.
The lower comparison uses the proved boundary-safe placement of every node. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

theorem acceptedStencil_in_cube (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) :
    acceptedStencil p T x₀ h ℓ r ⊆ Set.univ.pi (fun _ => Icc (0 : d → ℝ) 1) := by
  intro X hX i _
  have hg := physicalStencil_geometry p T x₀ (observedAnchorCoordinate p x₀ h X)
    (observedAuxiliaryCoordinates p x₀ r X) (observedPartnerCoordinate p x₀ ℓ X)
    hx hh hhsmall hℓ hℓr hrh
    (fun a => ⟨hX.1.1 a, hX.1.2 a⟩)
    (fun a => ⟨hX.2.1.1 a, hX.2.1.2 a⟩) hX.2.2 i
  rw [observedStencil_reconstruct p x₀ h ℓ r hh.ne' hℓ.ne' (hℓ.trans_le hℓr).ne' X] at hg
  exact ⟨fun a => (hg.1 a).1, fun a => (hg.1 a).2⟩

namespace RealOutcomeModel

variable {ε lower upper M₂ : ℝ} (M : RealOutcomeModel d ε lower upper M₂)

theorem design_product_upper_domination (I : Type*) [Fintype I] :
    Measure.pi (fun _ : I => M.design) ≤
      (upper.toNNReal ^ Fintype.card I) • (volume : Measure (I → d → ℝ)) := by
  apply finiteProduct_le_smul (fun _ : I => M.design) (fun _ => volume) upper.toNNReal
  intro i
  apply M.design_upper_domination.trans
  intro E
  change ENNReal.ofReal upper * (volume.restrict (Icc (0 : d → ℝ) 1)) E ≤
    ENNReal.ofReal upper * volume E
  exact mul_le_mul_left' (Measure.restrict_le_self E) _

theorem design_product_lower_domination (I : Type*) [Fintype I] :
    (lower.toNNReal ^ Fintype.card I) •
      (volume.restrict (Set.univ.pi (fun _ : I => Icc (0 : d → ℝ) 1))) ≤
      Measure.pi (fun _ : I => M.design) := by
  have h := finiteProduct_mono
    (fun _ : I => lower.toNNReal • volume.restrict (Icc (0 : d → ℝ) 1))
    (fun _ : I => M.design) (fun _ => M.design_lower_domination)
  rw [finiteProduct_smul] at h
  rw [← Measure.restrict_pi_pi] at h
  exact h

theorem design_product_event_bounds {I : Type*} [Fintype I]
    (E : Set (I → d → ℝ)) (hE : MeasurableSet E)
    (hcube : E ⊆ Set.univ.pi (fun _ : I => Icc (0 : d → ℝ) 1)) :
    ENNReal.ofReal lower ^ Fintype.card I * volume E ≤
      (Measure.pi (fun _ : I => M.design)) E ∧
    (Measure.pi (fun _ : I => M.design)) E ≤
      ENNReal.ofReal upper ^ Fintype.card I * volume E := by
  have hl := M.design_product_lower_domination I E
  have hu := M.design_product_upper_domination I E
  rw [Measure.smul_apply, Measure.restrict_apply hE, Set.inter_eq_left.mpr hcube] at hl
  rw [Measure.smul_apply] at hu
  simpa only [ENNReal.smul_def, ENNReal.coe_pow, ENNReal.ofReal] using And.intro hl hu

theorem acceptedStencil_probability_bounds (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4) :
    let V := ENNReal.ofReal (h / 4) ^ Fintype.card d *
      (ENNReal.ofReal ℓ ^ Fintype.card d *
        ENNReal.ofReal (2 * r * T.radius) ^
          (Fintype.card (TensorIndex d p) * Fintype.card d))
    ENNReal.ofReal lower ^ Fintype.card (StencilRole d p) * V ≤
      (Measure.pi (fun _ : StencilRole d p => M.design)) (acceptedStencil p T x₀ h ℓ r) ∧
    (Measure.pi (fun _ : StencilRole d p => M.design)) (acceptedStencil p T x₀ h ℓ r) ≤
      ENNReal.ofReal upper ^ Fintype.card (StencilRole d p) * V := by
  have hB := M.design_product_event_bounds (acceptedStencil p T x₀ h ℓ r)
    (acceptedStencil_measurable p T x₀ h ℓ r)
    (acceptedStencil_in_cube p T x₀ hx hh hhsmall hℓ hℓr hrh)
  rw [acceptedStencil_volume p T x₀ hh hℓ (hℓ.trans_le hℓr)] at hB
  exact hB

end RealOutcomeModel
end CausalLowerbound.UpperBound

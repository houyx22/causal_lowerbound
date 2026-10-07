import CausalLowerbound.PartC.CubicGhostIntegration
import CausalLowerbound.PartC.CubicObservationNormalization
import CausalLowerbound.PartC.PhysicalGhostOutcomePatterns

/-! Exact integration of normalized cubic observation patterns. The
finite observation expansion commutes with all actual ghost integrals,
and each block contributes precisely its selected-taper ghost weight. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry MvPolynomial Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d K P : Type*} [Fintype d] [DecidableEq d] [Fintype K] [DecidableEq K]
  [Fintype P] [DecidableEq P]

def normalizedPhysicalOutcomeCubicFunctional {I G : Type*} [Fintype I] [Fintype G]
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N τ : ℝ)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (g : G → d → ℝ) :
    MvPolynomial (Fin Q) ℝ →ₗ[ℝ] ℝ :=
  cubicSiteFunctional (fun f => selectedOutcomeGhostTaper Q e τ u f g *
    partialPhysicalOutcomePatternWeight x₀ ℓ r h k c w N B e u a ζ f g)

theorem outcome_ghost_cubic_pattern_integral
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : K → d → ℤ) (c w N τ : ℝ) (hc : 0 < c)
    (I G : K → Type*) [∀ k, Fintype (I k)] [∀ k, Fintype (G k)]
    (B : K → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (e : ∀ k, I k ⊕ G k ≃ Fin Q) (u : ∀ k, I k → d → ℝ) (a : ∀ k, I k → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (p : MvPolynomial (K × Fin Q) ℝ) :
    (∫ ghost : ∀ k, G k → d → ℝ, blockPolynomialFunctional
      (fun j => normalizedPhysicalOutcomeCubicFunctional Q x₀ ℓ r h (k j) c w N τ
        (B j) (e j) (u j) (a j) ζ (ghost j)) p
      ∂Measure.pi (fun j => Measure.pi (fun _ : G j => cubeMeasure d))) =
      blockPolynomialFunctional (fun j => cubicSiteFunctional (fun f =>
        ghostOutcomePatternIntegral x₀ ℓ r h (k j) c w N (B j) (e j) (u j) (a j) ζ f
          (selectedOutcomeGhostTaper Q (e j) τ (u j) f))) p := by
  let W := fun j (g : G j → d → ℝ) (f : Degree (Fin Q) 3) =>
    selectedOutcomeGhostTaper Q (e j) τ (u j) f g *
      partialPhysicalOutcomePatternWeight x₀ ℓ r h (k j) c w N (B j) (e j) (u j) (a j) ζ f g
  have hW (j : K) (f : Degree (Fin Q) 3) : Continuous (fun g => W j g f) :=
    (selectedOutcomeGhostTaper_continuous Q (e j) τ (u j) f).mul
      (partialPhysicalOutcomePatternWeight_continuous x₀ ℓ r h (k j) c w N hc
        (B j) (e j) (u j) (a j) ζ f)
  exact block_cubic_cube_integral G W hW p

theorem outcome_ghost_observation_expansion
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : K → d → ℤ) (c w N τ shift : ℝ) (hc : 0 < c)
    (I G : K → Type*) [∀ k, Fintype (I k)] [∀ k, Fintype (G k)]
    (B : K → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (e : ∀ k, I k ⊕ G k ≃ Fin Q) (u : ∀ k, I k → d → ℝ) (a : ∀ k, I k → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool)
    (b : P → Fin 4 → ℝ) (δ : P → K → ℝ) (slot : K → P → Fin Q) :
    (∫ ghost : ∀ k, G k → d → ℝ, blockPolynomialFunctional
      (fun j => normalizedPhysicalOutcomeCubicFunctional Q x₀ ℓ r h (k j) c w N τ
        (B j) (e j) (u j) (a j) ζ (ghost j))
      (∏ i, ∑ n : Fin 4, C (b i n) * (∑ j, C (shift * δ i j) * X (j, slot j i)) ^ n.val)
      ∂Measure.pi (fun j => Measure.pi (fun _ : G j => cubeMeasure d))) =
      cubicObservationExpansion (fun j f =>
        ghostOutcomePatternIntegral x₀ ℓ r h (k j) c w N (B j) (e j) (u j) (a j) ζ f
          (selectedOutcomeGhostTaper Q (e j) τ (u j) f)) b δ slot shift := by
  let p : MvPolynomial (K × Fin Q) ℝ :=
    ∏ i, ∑ n : Fin 4, C (b i n) * (∑ j, C (shift * δ i j) * X (j, slot j i)) ^ n.val
  let W := fun j (f : Degree (Fin Q) 3) =>
    ghostOutcomePatternIntegral x₀ ℓ r h (k j) c w N (B j) (e j) (u j) (a j) ζ f
      (selectedOutcomeGhostTaper Q (e j) τ (u j) f)
  have hint := outcome_ghost_cubic_pattern_integral Q x₀ ℓ r h k c w N τ hc I G B e u a ζ p
  have hexp : blockPolynomialFunctional (fun j => cubicSiteFunctional (W j)) p =
      cubicObservationExpansion W b δ slot shift :=
    block_cubic_observation_scaled_expansion W b δ slot shift
  exact hint.trans hexp

end CausalLowerbound.PartC

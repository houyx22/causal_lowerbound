import CausalLowerbound.PartC.CompletedOutcomeObservation
import CausalLowerbound.PartC.PropensityPatternIntegration

/-! Integrate the completed actual observation expansion. Continuity on
the compact ghost cubes justifies both coefficient averaging and the
finite cubic expansion, with the binary cell normalization retained. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem normalizedPhysicalOutcomeCubicFunctional_continuous
    {A G : Type*} [Fintype A] [Fintype G]
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N τ : ℝ) (hc : 0 < c)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (e : A ⊕ G ≃ Fin Q) (u : A → d → ℝ) (a : A → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (p : MvPolynomial (Fin Q) ℝ) :
    Continuous (fun g => normalizedPhysicalOutcomeCubicFunctional Q x₀ ℓ r h k c w N τ B e u a ζ g p) :=
  continuous_cubicSiteFunctional _ (fun f =>
    (selectedOutcomeGhostTaper_continuous Q e τ u f).mul
      (partialPhysicalOutcomePatternWeight_continuous x₀ ℓ r h k c w N hc B e u a ζ f)) p

def outcomeObservationPatternSum
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N a jb t τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) : ℝ :=
  (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)).expect (fun ξ =>
    (1 / 4 : ℝ) ^ Fintype.card I * cubicObservationExpansion
      (fun k => physicalGhostOutcomePatternWeight Q x₀ ℓ r h k.val c w N τ (B k) (e k)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) ζ ζ)
      (fun i => outcomeTaylorCoefficient (sign (y i).1) (sign (y i).2) 1 jb
        (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
        (a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
          (globalCarriedPolynomial Q S x₀ r (x i)))
        (physicalRoughField x₀ ℓ h ζ (x i)))
      (fun i k => linearPartition (localCoordinate x₀ r k.val (x i)))
      (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) (a * t))

theorem completed_outcome_pattern_integral
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N a jb t τ : ℝ) (hc : 0 < c)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    let P := fun ghost : ∀ k, G k → d → ℝ =>
      blockPolynomialFunctional (fun k => physicalOutcomePatternFunctional Q ρ x₀ ℓ r h k.val
        c w N t τ (B k) ζ (completedConfiguration (e k)
          (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)))
        (mixedOutcomeComponentPolynomial Q false S x₀ ℓ r h a jb t ζ x y)
    Integrable P (Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))) ∧
    (∫ ghost, P ghost ∂Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))) =
      outcomeObservationPatternSum Q hQ ρ S x₀ ℓ r h c w N a jb t τ B ζ x y G e := by
  dsimp only
  let μ := Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))
  let ν : FiniteLaw (S → MomentGrid (CoefficientExponent d Q) (4 * Q)) :=
    FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)
  let u := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
    carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
  let z := fun (k : S) i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (u k i)
  let L := fun (ghost : ∀ k, G k → d → ℝ) (k : S) =>
    normalizedPhysicalOutcomeCubicFunctional Q x₀ ℓ r h k.val c w N τ (B k) (e k) (u k) (z k) ζ (ghost k)
  let p := fun (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) =>
    ∏ i, outcomeTaylorPolynomial (sign (y i).1) (sign (y i).2) 1 jb
      (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
      (a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i)))
      (physicalRoughField x₀ ℓ h ζ (x i))
      (∑ k : S, C ((a * t) * linearPartition (localCoordinate x₀ r k.val (x i))) *
        X (k, retainedObservationSlot Q hQ x₀ r k.val x (e k) i))
  let f := fun ξ ghost => (1 / 4 : ℝ) ^ Fintype.card I * blockPolynomialFunctional (L ghost) (p ξ)
  have hf ξ : Integrable (f ξ) μ := by
    apply continuous_integrable_cubeBlocks G
    apply continuous_const.mul
    apply continuous_blockPolynomialFunctional
    intro k q
    exact (normalizedPhysicalOutcomeCubicFunctional_continuous Q x₀ ℓ r h k.val c w N τ hc
      (B k) (e k) (u k) (z k) ζ q).comp (continuous_apply k)
  have he : (fun ghost : ∀ k, G k → d → ℝ =>
      blockPolynomialFunctional (fun k => physicalOutcomePatternFunctional Q ρ x₀ ℓ r h k.val
        c w N t τ (B k) ζ (completedConfiguration (e k) (u k) (ghost k)))
        (mixedOutcomeComponentPolynomial Q false S x₀ ℓ r h a jb t ζ x y)) =
      (fun ghost => ν.expect (fun ξ => f ξ ghost)) := by
    funext ghost
    exact completed_outcome_normalized_expansion Q hQ ρ S x₀ ℓ r h c w N a jb t τ B ζ x y G e ghost
  rw [he]
  refine ⟨ν.expect_integrable μ f hf, ?_⟩
  rw [ν.integral_expect μ f hf]
  apply FiniteLaw.expect_congr
  intro ξ
  change (∫ ghost, (1 / 4 : ℝ) ^ Fintype.card I * blockPolynomialFunctional (L ghost) (p ξ) ∂μ) = _
  rw [integral_const_mul]
  apply congrArg (fun v : ℝ => (1 / 4 : ℝ) ^ Fintype.card I * v)
  dsimp only [p]
  simp_rw [outcomeTaylorPolynomial_eq_sum]
  exact outcome_ghost_observation_expansion Q x₀ ℓ r h (fun k : S => k.val) c w N τ (a * t) hc
    (fun k : S => {i // x i ∈ carrierBox x₀ r k.val}) G B e u z ζ
    (fun i => outcomeTaylorCoefficient (sign (y i).1) (sign (y i).2) 1 jb
      (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
      (a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))) (physicalRoughField x₀ ℓ h ζ (x i)))
    (fun i k => linearPartition (localCoordinate x₀ r k.val (x i)))
    (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k))

end CausalLowerbound.PartC

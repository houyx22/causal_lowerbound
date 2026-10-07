import CausalLowerbound.PartC.PropensityPatternIntegration
import CausalLowerbound.PartC.PropensityObservationWeights

/-! The actual raw observation mixture equals a finite sum of integrated
physical patterns. The labels and conditional coefficient kernels have
been integrated using their constructed moments; no ghost integral or
normalization factor remains implicit in this identity. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def propensityObservationPatternSum
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N ja b t τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) : ℝ :=
  (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)).expect (fun ξ =>
    ∑ s : I → Option S, propensityObservationCoefficient Q ρ side S x₀ ℓ r h ja b t ζ x y ξ s *
      ∏ k : S, physicalGhostPatternWeight Q x₀ ℓ r h k.val c w N ja τ (B k) (e k)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) ζ ζ
        ((observationChoiceSet s k).image (retainedObservationSlot Q hQ x₀ r k.val x (e k))))

theorem physical_propensity_raw_cell_expansion
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (side : Bool) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ ja b t τ K δ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀) (hθ : 0 ≤ θ) (hja : ja ^ 2 ≤ 1)
    (hcarr : ∀ k : S, HasPaperPropensityCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ ja t τ K δ)
    (R : ∀ k : S, PropensityMomentWitness Q ρ x₀ ℓ r h k.val c w N θ ja t τ)
    (x : I → d → ℝ) (y : I → Bool × Bool) (hcard : Fintype.card I ≤ Q)
    (G : S → Type) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    (signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (fun v =>
      ∏ i, (physicalCarrierProfile (ι := Fin Q) (D := 1) x₀ ℓ r h c w N N₀ θ
        hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S v.1.1) v.1.2).product S x₀ r (x i) *
          nuisanceCellMass (roughPropensityFields side S
            (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S v.2 k))
            x₀ ℓ r h ja b t v.1.2) (x i) (y i)) =
      independentSigns.expect (fun ζ =>
        (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (fun σ =>
          propensityObservationPatternSum Q hQ ρ side S x₀ ℓ r h c w N ja b t τ
            (fun k => (R k).representative) ζ x y G (fun k => (e k).trans (σ k).symm))) := by
  have he := physical_propensity_raw_cell_integral Q ρ side S x₀ ℓ r h c w N N₀ θ ja b t τ K δ
    hℓ hr hc hN₀ hN hm hrough hθ hcarr R x y hcard G e
  refine he.trans ?_
  apply FiniteLaw.expect_congr
  intro ζ
  let P := fun (σ : S → Equiv.Perm (Fin Q)) (ghost : ∀ k, G k → d → ℝ) =>
    blockPolynomialFunctional (fun k => physicalPropensityPatternFunctional Q ρ x₀ ℓ r h k.val
      c w N ja t τ (R k).representative ζ (completedConfiguration ((e k).trans (σ k).symm)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)))
      (mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y)
  have hp (σ : S → Equiv.Perm (Fin Q)) := completed_propensity_pattern_integral Q hQ ρ side S
    x₀ ℓ r h c w N N₀ ja b t τ hc hN₀ hN hm hrough hja (fun k => (R k).representative)
      ζ x y G (fun k => (e k).trans (σ k).symm)
  rw [FiniteLaw.integral_expect (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q)))
    (Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))) P (fun σ => (hp σ).1)]
  apply FiniteLaw.expect_congr
  intro σ
  exact (hp σ).2

end CausalLowerbound.PartC

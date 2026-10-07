import CausalLowerbound.PartC.IntegratedOutcomeObservation
import CausalLowerbound.PartC.PhysicalOutcomeRawCell

/-! The actual rough-outcome mixture under the constructed coefficient
kernels is exactly the finite normalized cubic observation expansion,
averaged over the paper coefficients and all slot permutations. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem physical_outcome_raw_cell_expansion
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t τ K δ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀) (hθ : 0 ≤ θ)
    (hcarr : ∀ k : S, HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ t τ K δ)
    (R : ∀ k : S, OutcomeMomentWitness Q ρ x₀ ℓ r h k.val c w N θ t τ)
    (x : I → d → ℝ) (y : I → Bool × Bool) (hcard : Fintype.card I ≤ Q)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    (signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (fun v =>
      ∏ i, (physicalCarrierProfile (ι := Fin Q) (D := 3) x₀ ℓ r h c w N N₀ θ
        hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S v.1.1) v.1.2).product S x₀ r (x i) *
          nuisanceCellMass (roughOutcomeFields false S
            (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S v.2 k))
            x₀ ℓ r h a jb t v.1.2) (x i) (y i)) =
      independentSigns.expect (fun ζ =>
        (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (fun σ =>
          outcomeObservationPatternSum Q hQ ρ S x₀ ℓ r h c w N a jb t τ
            (fun k => (R k).representative) ζ x y G (fun k => (e k).trans (σ k).symm))) := by
  have he := physical_outcome_raw_cell_integral Q ρ false S x₀ ℓ r h c w N N₀ θ a jb t τ K δ
    hℓ hr hc hN₀ hN hm hrough hθ hcarr R x y hcard G e
  refine he.trans ?_
  apply FiniteLaw.expect_congr
  intro ζ
  let P := fun (σ : S → Equiv.Perm (Fin Q)) (ghost : ∀ k, G k → d → ℝ) =>
    blockPolynomialFunctional (fun k => physicalOutcomePatternFunctional Q ρ x₀ ℓ r h k.val
      c w N t τ (R k).representative ζ (completedConfiguration ((e k).trans (σ k).symm)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)))
      (mixedOutcomeComponentPolynomial Q false S x₀ ℓ r h a jb t ζ x y)
  have hp (σ : S → Equiv.Perm (Fin Q)) := completed_outcome_pattern_integral Q hQ ρ S
    x₀ ℓ r h c w N a jb t τ hc (fun k => (R k).representative)
      ζ x y G (fun k => (e k).trans (σ k).symm)
  rw [FiniteLaw.integral_expect (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q)))
    (Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))) P (fun σ => (hp σ).1)]
  apply FiniteLaw.expect_congr
  intro σ
  exact (hp σ).2

end CausalLowerbound.PartC

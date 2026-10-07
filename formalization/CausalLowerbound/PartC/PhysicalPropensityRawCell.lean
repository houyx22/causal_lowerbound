import CausalLowerbound.PartC.RawPropensityPatternIntegral
import CausalLowerbound.PartC.MixedLikelihoodPolynomials

/-! Instantiate the raw integral identity with the actual physical design
and the actual binary cell probabilities. No polynomial interpolation,
moment identity, or integral-exchange assumption is added here. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I]

theorem physical_propensity_raw_cell_integral
    (Q : ℕ) (ρ : ℝ) (side : Bool) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ ja b t τ K δ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀) (hθ : 0 ≤ θ)
    (hcarr : ∀ k : S, HasPaperPropensityCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ ja t τ K δ)
    (R : ∀ k : S, PropensityMomentWitness Q ρ x₀ ℓ r h k.val c w N θ ja t τ)
    (x : I → d → ℝ) (y : I → Bool × Bool) (hQ : Fintype.card I ≤ Q)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    (signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (fun v =>
      ∏ i, (physicalCarrierProfile (ι := Fin Q) (D := 1) x₀ ℓ r h c w N N₀ θ
        hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S v.1.1) v.1.2).product S x₀ r (x i) *
          nuisanceCellMass (roughPropensityFields side S
            (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S v.2 k))
            x₀ ℓ r h ja b t v.1.2) (x i) (y i)) =
      independentSigns.expect (fun ζ =>
        ∫ ghost : ∀ k, G k → d → ℝ,
          (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (fun σ =>
            blockPolynomialFunctional (fun k => physicalPropensityPatternFunctional Q ρ x₀ ℓ r h k.val
              c w N ja t τ (R k).representative ζ (completedConfiguration ((e k).trans (σ k).symm)
                (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)))
              (mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y))
          ∂Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))) := by
  let F := fun v : (S → ℕ) × (activeBlocks (d := d) ℓ h → Bool) =>
    physicalCarrierProfile (ι := Fin Q) (D := 1) x₀ ℓ r h c w N N₀ θ
      hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S v.1) v.2
  have hF (labels : S → ℕ) (ζ : activeBlocks (d := d) ℓ h → Bool) (k : S) (u : d → ℝ) :
      (F (labels, ζ)).density k.val u =
        carrierPhysicalDensity (ι := Fin Q) (D := 1) x₀ ℓ r h k.val c w N θ (labels k) ζ u := by
    simp only [F, physicalCarrierProfile, extendBlockSample, dif_pos k.property]
  have hp (ζ : activeBlocks (d := d) ℓ h → Bool) :
      (mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y).totalDegree ≤ 4 * Q :=
    (mixedPropensityComponentPolynomial_degree Q side S x₀ ℓ r h ja b t ζ x y).trans (by omega)
  have he := raw_propensity_full_integral Q ρ S x₀ ℓ r h c w N N₀ θ ja t τ K δ hθ hcarr R F hF
    x G e (fun ζ => mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y) hp
  simp only [mixedPropensityComponentPolynomial_eval Q side S (paperCoefficientAtoms Q ρ)
    _ x₀ ℓ r h ja b t hr, ← Finset.prod_mul_distrib] at he
  rw [show (signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (fun v =>
      ∏ i, (physicalCarrierProfile (ι := Fin Q) (D := 1) x₀ ℓ r h c w N N₀ θ
        hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S v.1.1) v.1.2).product S x₀ r (x i) *
          nuisanceCellMass (roughPropensityFields side S
            (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S v.2 k))
            x₀ ℓ r h ja b t v.1.2) (x i) (y i)) = _ from he]
  apply FiniteLaw.expect_congr
  intro ζ
  apply integral_congr_ae
  filter_upwards [] with ghost
  simpa only [completedConfiguration_permute] using
    physical_propensity_block_permutations Q ρ x₀ ℓ r h (fun k : S => k.val) c w N θ ja t τ R ζ
      (fun k => completedConfiguration (e k)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k))
      (mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y)

end CausalLowerbound.PartC

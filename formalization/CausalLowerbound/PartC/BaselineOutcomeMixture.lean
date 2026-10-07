import CausalLowerbound.PartC.BaselineOutcomeGhostCarrier
import CausalLowerbound.PartC.PhysicalOutcomeRawCell
import CausalLowerbound.PartC.BaselinePropensityMixture

/-! The reference rough-outcome mixture keeps the constructed carrier
law and shared signs, with the fixed paper coefficient law. Its design
factor is exactly the zero cubic ghost pattern. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I]

theorem physical_outcome_reference_raw_cell
    (Q : ℕ) (ρ : ℝ) (side : Bool) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t τ C₀ δ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀) (hθ : 0 ≤ θ)
    (hcarr : ∀ k : S, HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ t τ C₀ δ)
    (R : ∀ k : S, OutcomeMomentWitness Q ρ x₀ ℓ r h k.val c w N θ t τ)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    (signBlockPrior (fun k => (R k).law) (fun _ _ _ => paperCoefficientLaw Q)).expect (fun v =>
      ∏ i, (physicalCarrierProfile (ι := Fin Q) (D := 3) x₀ ℓ r h c w N N₀ θ
        hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S v.1.1) v.1.2).product S x₀ r (x i) *
          nuisanceCellMass (roughOutcomeFields side S
            (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S v.2 k))
            x₀ ℓ r h a jb t v.1.2) (x i) (y i)) =
      independentSigns.expect (fun ζ =>
        (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)).expect (fun ξ =>
          (∏ k, ghostOutcomePatternIntegral x₀ ℓ r h k.val c w N (R k).representative (e k)
            (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
            (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
              (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) ζ 0 (fun _ => 1)) *
          ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
            (mixedOutcomeCellPolynomial Q side S x₀ ℓ r h a jb t ζ (x i) (y i)))) := by
  let F := fun v : (S → ℕ) × (activeBlocks (d := d) ℓ h → Bool) =>
    physicalCarrierProfile (ι := Fin Q) (D := 3) x₀ ℓ r h c w N N₀ θ
      hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S v.1) v.2
  let u := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
    carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
  let density := fun (k : S) ζ n => carrierTensor
    (fun m => carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k.val c w N θ m ζ) n (u k)
  let cells := fun ζ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) =>
    ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (mixedOutcomeCellPolynomial Q side S x₀ ℓ r h a jb t ζ (x i) (y i))
  have hF (labels : S → ℕ) ζ (k : S) (v : d → ℝ) :
      (F (labels, ζ)).density k.val v =
        carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k.val c w N θ (labels k) ζ v := by
    simp only [F, physicalCarrierProfile, extendBlockSample, dif_pos k.property]
  have hd (k : S) ζ n : |density k ζ n| ≤ (1 + θ) ^ Fintype.card {i // x i ∈ carrierBox x₀ r k.val} :=
    carrierTensor_abs_le _ (1 + θ) (fun m v => (hcarr k).density_abs_le m ζ v) n (u k)
  have hdesign (labels : S → ℕ) ζ : (∏ i, (F (labels, ζ)).product S x₀ r (x i)) =
      ∏ k, density k ζ (labels k) := by
    rw [CarrierProfile.sample_product_retained]
    simp only [hF, density, carrierTensor, u]
  have hcells ζ ξ : (∏ i, nuisanceCellMass (roughOutcomeFields side S
      (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S ξ k)) x₀ ℓ r h a jb t ζ) (x i) (y i)) = cells ζ ξ := by
    simp only [cells, mixedOutcomeCellPolynomial_eval Q side S (paperCoefficientAtoms Q ρ)
      ξ x₀ ℓ r h a jb t hr]
  change (signBlockPrior (fun k => (R k).law) (fun _ _ _ => paperCoefficientLaw Q)).expect
    (fun v => ∏ i, (F v.1).product S x₀ r (x i) * nuisanceCellMass (roughOutcomeFields side S
      (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S v.2 k)) x₀ ℓ r h a jb t v.1.2) (x i) (y i)) = _
  simp_rw [Finset.prod_mul_distrib, hdesign, hcells]
  rw [signBlockPrior_constant_kernel_product (fun k => (R k).law) (paperCoefficientLaw Q) density
    (fun k => (1 + θ) ^ Fintype.card {i // x i ∈ carrierBox x₀ r k.val})
    (fun k => pow_nonneg (by linarith) _) hd cells]
  apply FiniteLaw.expect_congr
  intro ζ
  rw [← FiniteLaw.expect_mul]
  apply FiniteLaw.expect_congr
  intro ξ
  apply congrArg (fun z : ℝ => z * cells ζ ξ)
  apply Finset.prod_congr rfl
  intro k _
  exact ((R k).untapered_zero_ghost_eq_carrierMarginal (hcarr k) hθ ζ (e k) (u k)
    (fun i => retained_design_chart_mem_cube x₀ r k.val x i)).symm

end CausalLowerbound.PartC


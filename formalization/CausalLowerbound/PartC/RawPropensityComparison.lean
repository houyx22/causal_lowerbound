import CausalLowerbound.PartC.BaselinePropensityMixture
import CausalLowerbound.PartC.AveragedPropensityComparison

/-! Compare the two actual raw observation mixtures. The perturbed side
uses the constructed coefficient kernels; the reference side keeps the
same carrier laws and signs with the paper coefficient law. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def physicalPropensityRawLikelihood
    (Q : ℕ) (ρ : ℝ) (side : Bool) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ ja b t : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀) (hθ : 0 ≤ θ)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (v : ((S → ℕ) × (activeBlocks (d := d) ℓ h → Bool)) ×
      (S → MomentGrid (CoefficientExponent d Q) (4 * Q))) : ℝ :=
  ∏ i, (physicalCarrierProfile (ι := Fin Q) (D := 1) x₀ ℓ r h c w N N₀ θ
    hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S v.1.1) v.1.2).product S x₀ r (x i) *
      nuisanceCellMass (roughPropensityFields side S
        (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S v.2 k))
        x₀ ℓ r h ja b t v.1.2) (x i) (y i)

theorem physical_propensity_raw_comparison_bound
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ ja b t τ C₀ δ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hw : 0 < w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hθ : 0 ≤ θ)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (hmb : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hja : 0 ≤ ja) (hsmall : ja * (1 + N₀) ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ht : 0 ≤ t) (hbtja : b * t ≤ ja)
    (hcarr : ∀ k : S, HasPaperPropensityCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ ja t τ C₀ δ)
    (R : ∀ k : S, PropensityMomentWitness Q ρ x₀ ℓ r h k.val c w N θ ja t τ)
    (x : I → d → ℝ) (y : I → Bool × Bool) (hcard : Fintype.card I ≤ Q)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (G : S → Type) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (hsmooth : ∀ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    let raw := fun side => physicalPropensityRawLikelihood Q ρ side S x₀ ℓ r h c w N N₀ θ ja b t
      hℓ hr hc hN₀ hN hmb hrough hθ x y
    |(signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (raw false) -
      (signBlockPrior (fun k => (R k).law) (fun _ _ _ => paperCoefficientLaw Q)).expect (raw true)| ≤
      (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (fun σ =>
        propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ
          (fun k => (R k).representative) x G (fun k => (e k).trans (σ k).symm)) := by
  dsimp only
  let raw := fun side => physicalPropensityRawLikelihood Q ρ side S x₀ ℓ r h c w N N₀ θ ja b t
    hℓ hr hc hN₀ hN hmb hrough hθ x y
  let reference := (signBlockPrior (fun k => (R k).law) (fun _ _ _ => paperCoefficientLaw Q)).expect (raw true)
  let F := fun ζ (σ : S → Equiv.Perm (Fin Q)) =>
    propensityObservationPatternSum Q hQ ρ false S x₀ ℓ r h c w N ja b t τ
      (fun k => (R k).representative) ζ x y G (fun k => (e k).trans (σ k).symm)
  let E := fun (σ : S → Equiv.Perm (Fin Q)) => propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ
    (fun k => (R k).representative) x G (fun k => (e k).trans (σ k).symm)
  have hja1 : ja ≤ 1 := (le_mul_of_one_le_right hja (by linarith : 1 ≤ 1 + N₀)).trans hsmall
  have hja2 : ja ^ 2 ≤ 1 := pow_le_one₀ hja hja1
  have hraw : (signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (raw false) =
      independentSigns.expect (fun ζ => (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (F ζ)) :=
    physical_propensity_raw_cell_expansion Q hQ ρ false S x₀ ℓ r h c w N N₀ θ ja b t τ C₀ δ
      hℓ hr hc hN₀ hN hmb hrough hθ hja2 hcarr R x y hcard G e
  have hbσ (σ : S → Equiv.Perm (Fin Q)) :
      |independentSigns.expect (fun ζ => F ζ σ) -
        independentSigns.expect (fun _ : activeBlocks (d := d) ℓ h → Bool => reference)| ≤ E σ := by
    rw [FiniteLaw.expect_const]
    have href := physical_propensity_reference_raw_cell Q ρ true S x₀ ℓ r h c w N N₀ θ ja b t τ C₀ δ
      hℓ hr hc hN₀ hN hmb hrough hθ hcarr R x y G (fun k => (e k).trans (σ k).symm)
    change reference = _ at href
    rw [href]
    have he := physical_propensity_pattern_average_bound Q hQ ρ S x₀ ℓ r h c w N N₀ ja b t τ
      hℓ hr hh hw hw1 hc hN₀ hN hm hmb hrough hja hsmall hb hb1 ht hbtja
      (fun k => (R k).representative) (fun k => (R k).norm_le) (fun k => (R k).reflection_fixed)
      x y hsep hcover htr G (fun k => (e k).trans (σ k).symm) hsmooth
    simpa only [F, E, propensityObservationUntaperedGhostProduct, observationChoiceSet_none,
      Finset.image_empty] using he
  have he := double_average_comparison_bound independentSigns
    (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))) F (fun _ _ => reference) E hbσ
  simp only [FiniteLaw.expect_const] at he
  change |(signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (raw false) - reference| ≤ _
  rw [hraw]
  exact he

end CausalLowerbound.PartC

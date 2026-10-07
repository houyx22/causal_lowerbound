import CausalLowerbound.PartC.AveragedOutcomeComparison
import CausalLowerbound.PartC.BaselineOutcomeMixture

/-! Compare the actual rough-outcome raw mixtures, using the constructed
coefficient kernels and the same carrier law with the fixed reference kernel. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def physicalOutcomeRawLikelihood
    (Q : ℕ) (ρ : ℝ) (side : Bool) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀) (hθ : 0 ≤ θ)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (v : ((S → ℕ) × (activeBlocks (d := d) ℓ h → Bool)) ×
      (S → MomentGrid (CoefficientExponent d Q) (4 * Q))) : ℝ :=
  ∏ i, (physicalCarrierProfile (ι := Fin Q) (D := 3) x₀ ℓ r h c w N N₀ θ
    hℓ hr hc hN₀ hN hm hrough hθ (extendBlockSample S v.1.1) v.1.2).product S x₀ r (x i) *
      nuisanceCellMass (roughOutcomeFields side S
        (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S v.2 k))
        x₀ ℓ r h a jb t v.1.2) (x i) (y i)

theorem physical_outcome_raw_comparison_bound
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t τ C₀ δ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hc : 0 < c)
    (hw : 0 < w) (hw1 : w ≤ 1) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hθ : 0 ≤ θ)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hidentity : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1) (hshift : 0 ≤ a * t) (hsjb : a * t ≤ jb)
    (hcarr : ∀ k : S, HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ t τ C₀ δ)
    (R : ∀ k : S, OutcomeMomentWitness Q ρ x₀ ℓ r h k.val c w N θ t τ)
    (x : I → d → ℝ) (y : I → Bool × Bool) (hcard : Fintype.card I ≤ Q)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (hsmooth : ∀ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    let raw := fun side => physicalOutcomeRawLikelihood Q ρ side S x₀ ℓ r h c w N N₀ θ a jb t
      hℓ hr hc hN₀ hN hm hrough hθ x y
    |(signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (raw false) -
      (signBlockPrior (fun k => (R k).law) (fun _ _ _ => paperCoefficientLaw Q)).expect (raw true)| ≤
      (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (fun σ =>
        outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ
          (fun k => (R k).representative) x G (fun k => (e k).trans (σ k).symm)) := by
  dsimp only
  let raw := fun side => physicalOutcomeRawLikelihood Q ρ side S x₀ ℓ r h c w N N₀ θ a jb t
    hℓ hr hc hN₀ hN hm hrough hθ x y
  let reference := (signBlockPrior (fun k => (R k).law) (fun _ _ _ => paperCoefficientLaw Q)).expect (raw true)
  let F := fun ζ (σ : S → Equiv.Perm (Fin Q)) =>
    outcomeObservationPatternSum Q hQ ρ S x₀ ℓ r h c w N a jb t τ
      (fun k => (R k).representative) ζ x y G (fun k => (e k).trans (σ k).symm)
  let E := fun (σ : S → Equiv.Perm (Fin Q)) => outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ
    (fun k => (R k).representative) x G (fun k => (e k).trans (σ k).symm)
  have hraw : (signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (raw false) =
      independentSigns.expect (fun ζ => (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (F ζ)) :=
    physical_outcome_raw_cell_expansion Q hQ ρ S x₀ ℓ r h c w N N₀ θ a jb t τ C₀ δ
      hℓ hr hc hN₀ hN hm hrough hθ hcarr R x y hcard G e
  have hbσ (σ : S → Equiv.Perm (Fin Q)) :
      |independentSigns.expect (fun ζ => F ζ σ) -
        independentSigns.expect (fun _ : activeBlocks (d := d) ℓ h → Bool => reference)| ≤ E σ := by
    rw [FiniteLaw.expect_const]
    have href := physical_outcome_reference_raw_cell Q ρ true S x₀ ℓ r h c w N N₀ θ a jb t τ C₀ δ
      hℓ hr hc hN₀ hN hm hrough hθ hcarr R x y G (fun k => (e k).trans (σ k).symm)
    change reference = _ at href
    rw [href]
    have he := physical_outcome_pattern_average_bound Q hQ ρ S x₀ ℓ r h c w N N₀ a jb t τ
      hℓ hr hh hc hw hw1 hN₀ hN hm hidentity hrough hjb hsmall hshift hsjb
      (fun k => (R k).representative) (fun k => (R k).norm_le) (fun k => (R k).reflection_fixed)
      x y hsep hcover htr G (fun k => (e k).trans (σ k).symm) hsmooth
    simpa only [F, E, outcomeObservationPatternWeight, Bool.false_eq_true, if_false] using he
  have he := double_average_comparison_bound independentSigns
    (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))) F (fun _ _ => reference) E hbσ
  simp only [FiniteLaw.expect_const] at he
  change |(signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (raw false) - reference| ≤ _
  rw [hraw]
  exact he

end CausalLowerbound.PartC

import CausalLowerbound.PartC.CrudeOutcomeComparison
import CausalLowerbound.PartC.RawOutcomeComparison

/-! The unrestricted cubic comparison for the actual observation mixture.
Both finite averages preserve the same constant times the target amplitude. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem physical_outcome_pattern_average_crude_bound
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ a jb t τ : ℝ) (hℓ : 0 < ℓ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1) (hshift : 0 ≤ a * t) (hsjb : a * t ≤ jb)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (hB : ∀ k, ‖B k‖ ≤ 2) (hreflect : ∀ k, reflection (B k) = B k)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (hsmooth : ∀ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    |independentSigns.expect (fun ζ => outcomeObservationPatternSum Q hQ ρ S x₀ ℓ r h c w N a jb t τ B ζ x y G e) -
      independentSigns.expect (fun ζ => (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)).expect (fun ξ =>
        (∏ k, outcomeObservationPatternWeight false Q S x₀ ℓ r h c w N τ B x G e ζ ζ k 0) *
          ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
            (mixedOutcomeCellPolynomial Q true S x₀ ℓ r h a jb t ζ (x i) (y i))))| ≤
      outcomeCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |a * t * jb| := by
  let f := fun ζ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) =>
    outcomeObservationValue true Q hQ S x₀ ℓ r h c w N jb (a * t) τ B x y
      (fun i => a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))) G e ζ ζ
  let g := fun ζ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) =>
    (∏ k, outcomeObservationPatternWeight false Q S x₀ ℓ r h c w N τ B x G e ζ ζ k 0) *
      eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (mixedOutcomeComponentPolynomial Q true S x₀ ℓ r h a jb t ζ x y)
  have he ξ : |independentSigns.expect (fun ζ => f ζ ξ) - independentSigns.expect (fun ζ => g ζ ξ)| ≤
      outcomeCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |a * t * jb| :=
    physical_outcome_observation_crude_bound Q hQ S (fun k => paperCoefficientAtoms Q ρ (ξ k))
      x₀ ℓ r h c w N N₀ a jb t τ hℓ hc hN₀ hN hm hrough hjb hsmall hshift hsjb
        B hB hreflect x y (hsmooth ξ) G e
  have hb := double_average_comparison_bound independentSigns
    (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)) f g
    (fun _ => outcomeCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |a * t * jb|) he
  simpa only [FiniteLaw.expect_const, f, g, outcomeObservationValue, outcomeObservationPatternSum,
    outcomeObservationPatternWeight, if_pos rfl, if_true, Bool.false_eq_true, if_false,
    mixedOutcomeComponentPolynomial, map_prod] using hb

theorem physical_outcome_raw_crude_bound
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t τ C₀ δ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hθ : 0 ≤ θ)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1) (hshift : 0 ≤ a * t) (hsjb : a * t ≤ jb)
    (hcarr : ∀ k : S, HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ t τ C₀ δ)
    (R : ∀ k : S, OutcomeMomentWitness Q ρ x₀ ℓ r h k.val c w N θ t τ)
    (x : I → d → ℝ) (y : I → Bool × Bool) (hcard : Fintype.card I ≤ Q)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (hsmooth : ∀ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    let raw := fun side => physicalOutcomeRawLikelihood Q ρ side S x₀ ℓ r h c w N N₀ θ a jb t
      hℓ hr hc hN₀ hN hm hrough hθ x y
    |(signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (raw false) -
      (signBlockPrior (fun k => (R k).law) (fun _ _ _ => paperCoefficientLaw Q)).expect (raw true)| ≤
      outcomeCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |a * t * jb| := by
  dsimp only
  let raw := fun side => physicalOutcomeRawLikelihood Q ρ side S x₀ ℓ r h c w N N₀ θ a jb t
    hℓ hr hc hN₀ hN hm hrough hθ x y
  let reference := (signBlockPrior (fun k => (R k).law) (fun _ _ _ => paperCoefficientLaw Q)).expect (raw true)
  let F := fun ζ (σ : S → Equiv.Perm (Fin Q)) =>
    outcomeObservationPatternSum Q hQ ρ S x₀ ℓ r h c w N a jb t τ
      (fun k => (R k).representative) ζ x y G (fun k => (e k).trans (σ k).symm)
  let E := outcomeCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |a * t * jb|
  have hraw : (signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (raw false) =
      independentSigns.expect (fun ζ => (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (F ζ)) :=
    physical_outcome_raw_cell_expansion Q hQ ρ S x₀ ℓ r h c w N N₀ θ a jb t τ C₀ δ
      hℓ hr hc hN₀ hN hm hrough hθ hcarr R x y hcard G e
  have hbσ (σ : S → Equiv.Perm (Fin Q)) :
      |independentSigns.expect (fun ζ => F ζ σ) -
        independentSigns.expect (fun _ : activeBlocks (d := d) ℓ h → Bool => reference)| ≤ E := by
    rw [FiniteLaw.expect_const]
    have href := physical_outcome_reference_raw_cell Q ρ true S x₀ ℓ r h c w N N₀ θ a jb t τ C₀ δ
      hℓ hr hc hN₀ hN hm hrough hθ hcarr R x y G (fun k => (e k).trans (σ k).symm)
    change reference = _ at href
    rw [href]
    have he := physical_outcome_pattern_average_crude_bound Q hQ ρ S x₀ ℓ r h c w N N₀ a jb t τ
      hℓ hc hN₀ hN hm hrough hjb hsmall hshift hsjb
      (fun k => (R k).representative) (fun k => (R k).norm_le) (fun k => (R k).reflection_fixed)
      x y G (fun k => (e k).trans (σ k).symm) hsmooth
    simpa only [F, E, outcomeObservationPatternWeight, Bool.false_eq_true, if_false] using he
  have he := double_average_comparison_bound independentSigns
    (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))) F (fun _ _ => reference) (fun _ => E) hbσ
  simp only [FiniteLaw.expect_const] at he
  change |(signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (raw false) - reference| ≤ E
  rw [hraw]
  exact he

end CausalLowerbound.PartC

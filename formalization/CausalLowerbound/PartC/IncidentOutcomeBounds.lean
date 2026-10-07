import CausalLowerbound.PartC.OutcomeExperimentRestriction
import CausalLowerbound.PartC.UniformOutcomeConstant

/-! Apply local outcome comparison to the actual incident blocks.
The original experiment and carrier witnesses are retained. Ghost slots
and effective assignment coverage are supplied by proved geometry. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]
  {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}

theorem outcome_witness_incident_crude_hellinger
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t τ C₀ δ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1)
    (hshift : 0 ≤ a * t) (hsjb : a * t ≤ jb)
    (hcarr : ∀ k : S, HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ t τ C₀ δ)
    (R : ∀ k : S, OutcomeMomentWitness Q ρ x₀ ℓ r h k.val c w N θ t τ)
    (hlegal : ∀ (T : Finset (d → ℤ)) side ζ (ξ : T → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (roughOutcomeFields side T (fun k => paperCoefficientAtoms Q ρ (extendBlockSample T ξ k))
        x₀ ℓ r h a jb t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 < κ) (x : I → d → ℝ) (hcard : Fintype.card I ≤ Q)
    (hsmooth : ∀ (T : Finset (d → ℤ)) (ξ : T → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q T x₀ r (x i))| ≤ 1) :
    let P := fun side => outcomeWitnessConditional Q ρ side S x₀ ℓ r h c w N N₀ θ a jb t τ
      hℓ hr hc hN₀ hN hθ hθ1 hm hrough R (hlegal S side) hκ.le x
    (P false).hellingerSq (P true) ≤
      outcomeLocalCrudeConstant Q (Fintype.card d) c N₀ θ κ * (a * t * jb) ^ 2 := by
  let T := configurationBlocks S x₀ r x
  have hTS : T ⊆ S := configurationBlocks_subset S x₀ r x
  let R' := fun k : T => R ⟨k.val, hTS k.property⟩
  let G := fun k : T => Fin (Q - Fintype.card {i // x i ∈ carrierBox x₀ r k.val})
  let e := fun k : T => retainedDesignCompletion Q x₀ r k.val x hcard
  have he (side : Bool) := outcomeWitnessConditional_configurationBlocks Q ρ side S x₀
    ℓ r h c w N N₀ θ a jb t τ hℓ hr hc hN₀ hN hθ hθ1 hm hrough R hκ.le x
    (hlegal S side) (hlegal T side)
  dsimp only
  rw [he false, he true]
  have hbnd := outcome_witness_conditional_crude_hellinger Q hQ ρ T x₀ ℓ r h c w N N₀ θ a jb t τ C₀ δ
    hℓ hr hc hN₀ hN hθ hθ1 hm hrough hjb hsmall hshift hsjb
    (fun k => hcarr ⟨k.val, hTS k.property⟩) R' (hlegal T) hκ x hcard G e (hsmooth T)
  have hout : (Fintype.card (I → Bool × Bool) : ℝ) = (4 : ℝ) ^ Fintype.card I := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Nat.cast_pow]
    norm_num
  dsimp only at hbnd
  rw [hout, outcomeCrudeHellingerCoefficient_mul_sq] at hbnd
  have hk : Fintype.card T ≤ Q * 5 ^ Fintype.card d := by
    simpa only [T, Fintype.card_coe] using (configurationBlocks_card_le S x₀ r x).trans
      (Nat.mul_le_mul_right (5 ^ Fintype.card d) hcard)
  exact hbnd.trans (mul_le_mul_of_nonneg_right
    (outcomeCrudeHellingerCoefficient_le_uniform Q (Fintype.card I) (Fintype.card T)
      (Fintype.card d) c N₀ θ κ hcard hk) (sq_nonneg _))

theorem outcome_witness_incident_good_hellinger
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t τ C₀ δ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hw : 0 < w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (hmb : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1)
    (hshift : 0 ≤ a * t) (hsjb : a * t ≤ jb)
    (hcarr : ∀ k : activeBlocks (d := d) r h,
      HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ t τ C₀ δ)
    (R : ∀ k : activeBlocks (d := d) r h,
      OutcomeMomentWitness Q ρ x₀ ℓ r h k.val c w N θ t τ)
    (hlegal : ∀ (T : Finset (d → ℤ)) side ζ (ξ : T → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (roughOutcomeFields side T (fun k => paperCoefficientAtoms Q ρ (extendBlockSample T ξ k))
        x₀ ℓ r h a jb t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 < κ) (x : I → d → ℝ) (hcard : Fintype.card I ≤ Q)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 →
      x i ∉ assignmentTransitionUnion (activeBlocks r h) w x₀ r)
    (hsmooth : ∀ (T : Finset (d → ℤ)) (ξ : T → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |a * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q T x₀ r (x i))| ≤ 1) :
    let S := activeBlocks (d := d) r h
    let T := configurationBlocks S x₀ r x
    let R' := fun k : T => R ⟨k.val, configurationBlocks_subset S x₀ r x k.property⟩
    let G := fun k : T => Fin (Q - Fintype.card {i // x i ∈ carrierBox x₀ r k.val})
    let e := fun k : T => retainedDesignCompletion Q x₀ r k.val x hcard
    let E := (FiniteLaw.independent (fun _ : T => permutationLaw (Fin Q))).expect (fun σ =>
      outcomeObservationComparisonError Q T x₀ ℓ r h c N N₀ a jb t τ
        (fun k => (R' k).representative) x G (fun k => (e k).trans (σ k).symm))
    let P := fun side => outcomeWitnessConditional Q ρ side S x₀ ℓ r h c w N N₀ θ a jb t τ
      hℓ hr hc hN₀ hN hθ hθ1 hmb hrough R (hlegal S side) hκ.le x
    (P false).hellingerSq (P true) ≤ (Fintype.card (I → Bool × Bool) : ℝ) *
      (E / ((1 - θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I) ^ 2 / (κ ^ 2) ^ Fintype.card I := by
  let S := activeBlocks (d := d) r h
  let T := configurationBlocks S x₀ r x
  have hTS : T ⊆ S := configurationBlocks_subset S x₀ r x
  let R' := fun k : T => R ⟨k.val, hTS k.property⟩
  let G := fun k : T => Fin (Q - Fintype.card {i // x i ∈ carrierBox x₀ r k.val})
  let e := fun k : T => retainedDesignCompletion Q x₀ r k.val x hcard
  have he (side : Bool) := outcomeWitnessConditional_configurationBlocks Q ρ side S x₀
    ℓ r h c w N N₀ θ a jb t τ hℓ hr hc hN₀ hN hθ hθ1 hmb hrough R hκ.le x
    (hlegal S side) (hlegal T side)
  dsimp only
  rw [he false, he true]
  exact outcome_witness_conditional_good_hellinger Q hQ ρ T x₀ ℓ r h c w N N₀ θ a jb t τ C₀ δ
    hℓ hr hh hw hw1 hc hN₀ hN hθ hθ1 hm hmb hrough hjb hsmall hshift hsjb
    (fun k => hcarr ⟨k.val, hTS k.property⟩) R' (hlegal T) hκ x hcard hsep
    (configurationBlocks_supported_cover w hw hw1 x₀ r h hr hh x)
    (fun i hi => configurationBlocks_off_transition S w x₀ r x i (htr i hi)) G e (hsmooth T)

end CausalLowerbound.PartC


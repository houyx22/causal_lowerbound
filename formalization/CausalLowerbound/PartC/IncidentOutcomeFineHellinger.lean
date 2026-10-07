import CausalLowerbound.PartC.IncidentOutcomeBounds
import CausalLowerbound.PartC.OutcomeFineBound

/-! The actual normalized outcome experiments on a small component
satisfy the geometric Hellinger bound. Its coefficient is independent of
the full sample size and total active-block count. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]
  {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}

theorem outcome_witness_incident_fine_hellinger
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a jb t τ C₀ δ M : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hw : 0 < w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (hmb : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1)
    (hshift : 0 ≤ a * t) (hsjb : a * t ≤ jb) (hM : 0 ≤ M)
    (hcarr : ∀ k : activeBlocks (d := d) r h,
      HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ t τ C₀ δ)
    (R : ∀ k : activeBlocks (d := d) r h,
      OutcomeMomentWitness Q ρ x₀ ℓ r h k.val c w N θ t τ)
    (hsym : ∀ k j, ‖symbolPart j (R k).representative‖ ≤ M * (ℓ / (2 * r)) ^ Fintype.card d)
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
    let G := fun k : T => Fin (Q - Fintype.card {i // x i ∈ carrierBox x₀ r k.val})
    let e := fun k : T => retainedDesignCompletion Q x₀ r k.val x hcard
    let P := fun side => outcomeWitnessConditional Q ρ side S x₀ ℓ r h c w N N₀ θ a jb t τ
      hℓ hr hc hN₀ hN hθ hθ1 hmb hrough R (hlegal S side) hκ.le x
    (P false).hellingerSq (P true) ≤ outcomeLocalFineConstant Q (Fintype.card d) c N₀ M θ κ *
      (a * t * jb) ^ 2 * ((Fintype.card T : ℝ) * ((ℓ / (2 * r)) ^ Fintype.card d) ^ 2 +
        propensityGhostDefectSum Q T x₀ r τ x G e) := by
  let S := activeBlocks (d := d) r h
  let T := configurationBlocks S x₀ r x
  let R' := fun k : T => R ⟨k.val, configurationBlocks_subset S x₀ r x k.property⟩
  let G := fun k : T => Fin (Q - Fintype.card {i // x i ∈ carrierBox x₀ r k.val})
  let e := fun k : T => retainedDesignCompletion Q x₀ r k.val x hcard
  have hbnd := outcome_witness_incident_good_hellinger Q hQ ρ x₀ ℓ r h c w N N₀ θ a jb t τ C₀ δ
    hℓ hr hh hw hw1 hc hN₀ hN hθ hθ1 hm hmb hrough hjb hsmall hshift hsjb
    hcarr R hlegal hκ x hcard hsep htr hsmooth
  dsimp only at hbnd ⊢
  rw [outcomeObservationComparisonError_permutation_average] at hbnd
  have hout : (Fintype.card (I → Bool × Bool) : ℝ) = (4 : ℝ) ^ Fintype.card I := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Nat.cast_pow]
    norm_num
  rw [hout] at hbnd
  have hfine := outcomeComparisonError_fine_hellinger_bound Q T x₀ ℓ r h c N N₀ a jb t τ M θ κ
    hℓ.le hr hc hN₀ hN hM hshift hjb (fun k => (R' k).representative) (fun k => (R' k).norm_le)
    (fun k j => hsym _ j) x G e
  have hk : Fintype.card T ≤ Q * 5 ^ Fintype.card d := by
    simpa only [T, Fintype.card_coe] using (configurationBlocks_card_le S x₀ r x).trans
      (Nat.mul_le_mul_right (5 ^ Fintype.card d) hcard)
  have hcost : 0 ≤ (Fintype.card T : ℝ) * ((ℓ / (2 * r)) ^ Fintype.card d) ^ 2 +
      propensityGhostDefectSum Q T x₀ r τ x G e :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (propensityGhostDefectSum_bounds Q T x₀ r τ x G e).1
  exact hbnd.trans (hfine.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (outcomeFineHellingerCoefficient_le_uniform Q
      (Fintype.card I) (Fintype.card T) (Fintype.card d) c N₀ M θ κ hcard hk) (sq_nonneg _)) hcost))

end CausalLowerbound.PartC


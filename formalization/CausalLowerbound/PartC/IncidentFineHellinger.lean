import CausalLowerbound.PartC.IncidentPropensityBounds
import CausalLowerbound.PartC.PropensityFineBound

/-! The actual normalized propensity experiments on a small component
satisfy the geometric Hellinger bound. Its coefficient is independent of
the full sample size and total active-block count. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]
  {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}

theorem propensity_witness_incident_fine_hellinger
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ ja b t τ C₀ δ M : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hw : 0 < w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (hmb : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hja : 0 ≤ ja) (hsmall : ja * (1 + N₀) ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ht : 0 ≤ t) (hbtja : b * t ≤ ja) (hM : 0 ≤ M)
    (hcarr : ∀ k : activeBlocks (d := d) r h,
      HasPaperPropensityCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ ja t τ C₀ δ)
    (R : ∀ k : activeBlocks (d := d) r h,
      PropensityMomentWitness Q ρ x₀ ℓ r h k.val c w N θ ja t τ)
    (hsym : ∀ k j, ‖symbolPart j (R k).representative‖ ≤ M * (ℓ / (2 * r)) ^ Fintype.card d)
    (hlegal : ∀ (T : Finset (d → ℤ)) side ζ (ξ : T → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (roughPropensityFields side T (fun k => paperCoefficientAtoms Q ρ (extendBlockSample T ξ k))
        x₀ ℓ r h ja b t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 < κ) (x : I → d → ℝ) (hcard : Fintype.card I ≤ Q)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 →
      x i ∉ assignmentTransitionUnion (activeBlocks r h) w x₀ r)
    (hsmooth : ∀ (T : Finset (d → ℤ)) (ξ : T → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q T x₀ r (x i))| ≤ 1) :
    let S := activeBlocks (d := d) r h
    let T := configurationBlocks S x₀ r x
    let G := fun k : T => Fin (Q - Fintype.card {i // x i ∈ carrierBox x₀ r k.val})
    let e := fun k : T => retainedDesignCompletion Q x₀ r k.val x hcard
    let P := fun side => propensityWitnessConditional Q ρ side S x₀ ℓ r h c w N N₀ θ ja b t τ
      hℓ hr hc hN₀ hN hθ hθ1 hmb hrough R (hlegal S side) hκ.le x
    (P false).hellingerSq (P true) ≤ propensityLocalFineConstant Q (Fintype.card d) c N₀ M θ κ *
      (ja * b * t) ^ 2 * ((Fintype.card T : ℝ) * ((ℓ / (2 * r)) ^ Fintype.card d) ^ 2 +
        propensityGhostDefectSum Q T x₀ r τ x G e) := by
  let S := activeBlocks (d := d) r h
  let T := configurationBlocks S x₀ r x
  let R' := fun k : T => R ⟨k.val, configurationBlocks_subset S x₀ r x k.property⟩
  let G := fun k : T => Fin (Q - Fintype.card {i // x i ∈ carrierBox x₀ r k.val})
  let e := fun k : T => retainedDesignCompletion Q x₀ r k.val x hcard
  have hbnd := propensity_witness_incident_good_hellinger Q hQ ρ x₀ ℓ r h c w N N₀ θ ja b t τ C₀ δ
    hℓ hr hh hw hw1 hc hN₀ hN hθ hθ1 hm hmb hrough hja hsmall hb hb1 ht hbtja
    hcarr R hlegal hκ x hcard hsep htr hsmooth
  dsimp only at hbnd ⊢
  rw [propensityComparisonError_permutation_average] at hbnd
  have hout : (Fintype.card (I → Bool × Bool) : ℝ) = (4 : ℝ) ^ Fintype.card I := by
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Nat.cast_pow]
    norm_num
  rw [hout] at hbnd
  have hfine := propensityComparisonError_fine_hellinger_bound Q T x₀ ℓ r h c N N₀ ja b t τ M θ κ
    hℓ.le hr hc hN₀ hN hM hja hb ht (fun k => (R' k).representative) (fun k => (R' k).norm_le)
    (fun k j => hsym _ j) x G e
  have hk : Fintype.card T ≤ Q * 5 ^ Fintype.card d := by
    simpa only [T, Fintype.card_coe] using (configurationBlocks_card_le S x₀ r x).trans
      (Nat.mul_le_mul_right (5 ^ Fintype.card d) hcard)
  have hcost : 0 ≤ (Fintype.card T : ℝ) * ((ℓ / (2 * r)) ^ Fintype.card d) ^ 2 +
      propensityGhostDefectSum Q T x₀ r τ x G e :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (propensityGhostDefectSum_bounds Q T x₀ r τ x G e).1
  exact hbnd.trans (hfine.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (propensityFineHellingerCoefficient_le_uniform Q
      (Fintype.card I) (Fintype.card T) (Fintype.card d) c N₀ M θ κ hcard hk) (sq_nonneg _)) hcost))

end CausalLowerbound.PartC

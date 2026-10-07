import CausalLowerbound.PartC.GlobalOutcomeCost
import CausalLowerbound.PartC.BadComponentCosts
import CausalLowerbound.PartC.OutcomeComponentHellinger
import CausalLowerbound.PartC.SharedClusterProbability

/-! The actual degree-three conditional experiment is bounded by the
measurable global cost outside the proved large-component exception.
All component restrictions, completions, counts, and bad-configuration
costs are derived from the physical dependency graph. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt incidenceComponentFintype
variable {d : Type*} [Fintype d] [DecidableEq d]
  {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}

theorem outcome_witness_global_conditional_hellinger
    (H₀ : DiscreteLaw ℕ) (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a₀ jb t τ C₀ δ M : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hℓr : ℓ ≤ r) (hrh : r ≤ h) (hw : 0 < w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (hmb : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1)
    (hshift : 0 ≤ a₀ * t) (hsjb : a₀ * t ≤ jb) (hM : 0 ≤ M)
    (hcarr : ∀ k : activeBlocks (d := d) r h,
      HasPaperOutcomeCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ t τ C₀ δ)
    (R : ∀ k : activeBlocks (d := d) r h,
      OutcomeMomentWitness Q ρ x₀ ℓ r h k.val c w N θ t τ)
    (hsym : ∀ k j, ‖symbolPart j (R k).representative‖ ≤ M * (ℓ / (2 * r)) ^ Fintype.card d)
    (hlegal : ∀ (T : Finset (d → ℤ)) side ζ (ξ : T → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (roughOutcomeFields side T (fun k => paperCoefficientAtoms Q ρ (extendBlockSample T ξ k))
        x₀ ℓ r h a₀ jb t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 < κ) (n : ℕ) (x : Fin n → d → ℝ) (hx : x ∉ sharedLargeClusterEvent n Q x₀ r h)
    (hsmooth : ∀ (T : Finset (d → ℤ)) (ξ : T → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |a₀ * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q T x₀ r (x i))| ≤ 1) :
    let S := activeBlocks (d := d) r h
    let P := fun side => outcomeWitnessConditional Q ρ side S x₀ ℓ r h c w N N₀ θ a₀ jb t τ
      hℓ hr hc hN₀ hN hθ hθ1 hmb hrough R (hlegal S side) hκ.le x
    (P false).hellingerSq (P true) ≤ outcomeGlobalCost H₀ Q x₀ ℓ r h c N₀ M θ κ a₀ jb t τ w x := by
  let S := activeBlocks (d := d) r h
  let inc := physicalSharedIncidence S x₀ ℓ r h x
  let xc := fun a : Option (incidenceGraph inc).ConnectedComponent =>
    fun i : {i // siteComponent inc i = a} => x i.val
  let T := fun a : Option (incidenceGraph inc).ConnectedComponent => configurationBlocks S x₀ r (xc a)
  have hcard (a : Option (incidenceGraph inc).ConnectedComponent) :
      Fintype.card {i // siteComponent inc i = a} ≤ Q :=
    shared_component_fiber_small_off_largeCluster n Q hQ x₀ ℓ r h hℓ hr hℓr hrh x hx a
  let dg := fun a : Option (incidenceGraph inc).ConnectedComponent =>
    propensityGhostDefectSum Q (T a) x₀ r τ (xc a)
      (fun k => Fin (Q - Fintype.card {i // xc a i ∈ carrierBox x₀ r k.val}))
      (fun k => retainedDesignCompletion Q x₀ r k.val (xc a) (hcard a))
  let g := (ℓ / (2 * r)) ^ Fintype.card d
  let CF := outcomeLocalFineConstant Q (Fintype.card d) c N₀ M θ κ * (a₀ * t * jb) ^ 2
  let CC := outcomeLocalCrudeConstant Q (Fintype.card d) c N₀ θ κ * (a₀ * t * jb) ^ 2
  have hCF : 0 ≤ CF := mul_nonneg (outcomeLocalFineConstant_nonneg Q (Fintype.card d) c N₀ M θ κ) (sq_nonneg _)
  have hCC : 0 ≤ CC := mul_nonneg (outcomeLocalCrudeConstant_nonneg Q (Fintype.card d) c N₀ θ κ) (sq_nonneg _)
  let P := fun (side : Bool) (a : Option (incidenceGraph inc).ConnectedComponent) =>
    outcomeWitnessConditional Q ρ side S x₀ ℓ r h c w N N₀ θ a₀ jb t τ
      hℓ hr hc hN₀ hN hθ hθ1 hmb hrough R (hlegal S side) hκ.le (xc a)
  have hd0 (a : Option (incidenceGraph inc).ConnectedComponent) : 0 ≤ dg a :=
    (propensityGhostDefectSum_bounds Q (T a) x₀ r τ (xc a) _ _).1
  have hlocal (a : Option (incidenceGraph inc).ConnectedComponent) :
      (P false a).hellingerSq (P true a) ≤ CF * ((Fintype.card (T a) : ℝ) * g ^ 2 + dg a) +
        CC * (if propensityGoodConfiguration w x₀ ℓ r h (xc a) then 0 else 1) := by
    by_cases hg : propensityGoodConfiguration w x₀ ℓ r h (xc a)
    · rw [if_pos hg, mul_zero, add_zero]
      exact outcome_witness_incident_fine_hellinger Q hQ ρ x₀ ℓ r h c w N N₀ θ a₀ jb t τ C₀ δ M
        hℓ hr (hr.trans_le hrh) hw hw1 hc hN₀ hN hθ hθ1 hm hmb hrough hjb hsmall hshift hsjb hM
        hcarr R hsym hlegal hκ (xc a) (hcard a) hg.1 hg.2 (fun T ξ i => hsmooth T ξ i.val)
    · rw [if_neg hg, mul_one]
      apply (outcome_witness_incident_crude_hellinger Q hQ ρ S x₀ ℓ r h c w N N₀ θ a₀ jb t τ C₀ δ
        hℓ hr hc hN₀ hN hθ hθ1 hmb hrough hjb hsmall hshift hsjb hcarr R hlegal hκ
        (xc a) (hcard a) (fun T ξ i => hsmooth T ξ i.val)).trans
      exact le_add_of_nonneg_left (mul_nonneg hCF
        (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (hd0 a)))
  have hblocks : (∑ a : Option (incidenceGraph inc).ConnectedComponent, (Fintype.card (T a) : ℝ)) ≤
      (5 : ℝ) ^ Fintype.card d * observationSetCount (coordinateBox x₀ (5 * h)) x := by
    simpa only [T, xc, Fintype.card_coe] using
      shared_component_block_card_sum_le_coarse_count x₀ ℓ r h hr hrh x
  have hghost : (∑ a : Option (incidenceGraph inc).ConnectedComponent, dg a) ≤
      globalGhostCost H₀ Q 0 τ x₀ r h x :=
    shared_component_ghost_sum_le_globalGhostCost H₀ Q τ x₀ ℓ r h hr x hcard
  have hgeo : (∑ a : Option (incidenceGraph inc).ConnectedComponent, (Fintype.card (T a) : ℝ)) * g ^ 2 +
      (∑ a : Option (incidenceGraph inc).ConnectedComponent, dg a) ≤
      (5 : ℝ) ^ Fintype.card d * g ^ 2 * observationSetCount (coordinateBox x₀ (5 * h)) x +
        globalGhostCost H₀ Q 0 τ x₀ r h x := by
    apply add_le_add _ hghost
    exact (mul_le_mul_of_nonneg_right hblocks (sq_nonneg _)).trans_eq (by ring)
  dsimp only
  calc
    _ ≤ ∑ a : Option (incidenceGraph inc).ConnectedComponent, (P false a).hellingerSq (P true a) :=
      outcome_witness_component_hellinger Q ρ S x₀ ℓ r h c w N N₀ θ a₀ jb t τ
        hℓ hr hc hN₀ hN hθ hθ1 hmb hrough R (hlegal S) hκ.le x
    _ ≤ ∑ a : Option (incidenceGraph inc).ConnectedComponent,
        (CF * ((Fintype.card (T a) : ℝ) * g ^ 2 + dg a) +
          CC * (if propensityGoodConfiguration w x₀ ℓ r h (xc a) then 0 else 1)) :=
      Finset.sum_le_sum (fun a _ => hlocal a)
    _ = CF * ((∑ a : Option (incidenceGraph inc).ConnectedComponent, (Fintype.card (T a) : ℝ)) * g ^ 2 +
        ∑ a : Option (incidenceGraph inc).ConnectedComponent, dg a) +
          CC * propensityBadComponentCount w x₀ ℓ r h x := by
      simp only [propensityBadComponentCount, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      rfl
    _ ≤ outcomeGlobalCost H₀ Q x₀ ℓ r h c N₀ M θ κ a₀ jb t τ w x :=
      add_le_add (mul_le_mul_of_nonneg_left hgeo hCF)
        (mul_le_mul_of_nonneg_left (propensityBadComponentCount_le w x₀ ℓ r h hℓ hr hℓr hrh x) hCC)

end CausalLowerbound.PartC


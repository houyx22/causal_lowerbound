import CausalLowerbound.PartC.OutcomeJointComparison
import CausalLowerbound.PartC.PropensityCostAlgebra

/-! A finite-sample minimax bound from the constructed outcome
experiment. The remaining numerical condition involves only explicit
scale monomials, not total variation or a likelihood matching premise. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
  {α β γ : Regularity} {Lπ L₀ Lτ κ lower upper : ℝ}

theorem outcome_witness_minimax_of_numeric_bound
    (H₀ : DiscreteLaw ℕ) (q : ℕ) (ρ : ℝ) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ a₀ jb t τ C₀ δ M v : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hℓr : ℓ ≤ r) (hrh : r ≤ h) (hw : 0 < w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hv : 0 < v) (hvd : v < (Fintype.card d : ℝ)) (hτ : 0 < τ)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (hmb : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1)
    (hshift : 0 ≤ a₀ * t) (hsjb : a₀ * t ≤ jb) (hM : 0 ≤ M)
    (hcarr : ∀ k : activeBlocks (d := d) r h,
      HasPaperOutcomeCarrier (q + 1) ρ x₀ ℓ r h k.val c w N N₀ θ t τ C₀ δ)
    (R : ∀ k : activeBlocks (d := d) r h,
      OutcomeMomentWitness (q + 1) ρ x₀ ℓ r h k.val c w N θ t τ)
    (hsym : ∀ k j, ‖symbolPart j (R k).representative‖ ≤ M * (ℓ / (2 * r)) ^ Fintype.card d)
    (hlegal : ∀ (T : Finset (d → ℤ)) side ζ
      (ξ : T → MomentGrid (CoefficientExponent d (q + 1)) (4 * (q + 1))),
      (roughOutcomeFields side T (fun k => paperCoefficientAtoms (q + 1) ρ (extendBlockSample T ξ k))
        x₀ ℓ r h a₀ jb t ζ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 < κ)
    (hlo : lower ≤ (1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d))
    (hhi : (1 + θ) ^ (5 ^ Fintype.card d) / (1 - θ) ^ (5 ^ Fintype.card d) ≤ upper)
    (n : ℕ) (hnr : (n : ℝ) * r ^ Fintype.card d ≤ 1)
    (hsmooth : ∀ (T : Finset (d → ℤ))
      (ξ : T → MomentGrid (CoefficientExponent d (q + 1)) (4 * (q + 1))) x,
      |a₀ * eval (fun ka => paperCoefficientAtoms (q + 1) ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial (q + 1) T x₀ r x)| ≤ 1)
    (hbudget : sharedClusterProbabilityConstant d (q + 1) θ *
      ((n : ℝ) ^ ((q + 1) + 1) * h ^ Fintype.card d * r ^ ((q + 1) * Fintype.card d)) +
      Real.sqrt (propensityScalarCost (Fintype.card d)
        (outcomeLocalFineConstant (q + 1) (Fintype.card d) c N₀ M θ κ)
        (outcomeLocalCrudeConstant (q + 1) (Fintype.card d) c N₀ θ κ)
        (designDensityCeiling d θ) (globalGhostConstant d q θ v) ℓ r h n (a₀ * t * jb) (τ ^ v) w) ≤ 1 / 2) :
    ENNReal.ofReal (a₀ * t * jb / 4) ≤ minimaxRisk α β γ Lπ L₀ Lτ κ lower upper hκ.le x₀ n := by
  let S := activeBlocks (d := d) r h
  let F := fun z : (S → ℕ) × (activeBlocks (d := d) ℓ h → Bool) =>
    physicalCarrierProfile (ι := Fin (q + 1)) (D := 3) x₀ ℓ r h c w N N₀ θ
      hℓ hr hc hN₀ hN hmb hrough hθ (extendBlockSample S z.1) z.2
  let kernel := fun (side : Bool) (k : S) ζ m =>
    if side then paperCoefficientLaw (q + 1) else (R k).kernel ζ m
  let models := fun (side : Bool)
    (z : ((S → ℕ) × (activeBlocks (d := d) ℓ h → Bool)) ×
      (S → MomentGrid (CoefficientExponent d (q + 1)) (4 * (q + 1)))) =>
    roughOutcomeStatisticalModel side S (paperCoefficientAtoms (q + 1) ρ) z.2 x₀ ℓ r h a₀ jb t z.1.2
      (F z.1) hθ hθ1 (hlegal S side z.1.2 z.2) ((F z.1).designLegal hθ hθ1 hlo hhi S x₀ r)
  let μ := mixedCarrierDesign F hθ hθ1 S x₀ r (fun k => (R k).law)
    (fun _ _ _ => paperCoefficientLaw (d := d) (q + 1)) n
  let P := fun side => carrierComparisonDensity F hθ hθ1 S x₀ r (fun k => (R k).law)
    (paperCoefficientLaw (q + 1)) (kernel side) n (models side) hκ.le
  have htv : (P false).totalVariation (P true) ≤
      μ.real (sharedLargeClusterEvent n (q + 1) x₀ r h) +
        Real.sqrt (∫ x, outcomeGlobalCost H₀ (q + 1) x₀ ℓ r h c N₀ M θ κ a₀ jb t τ w x ∂μ) :=
    outcome_witness_model_totalVariation_le H₀ (q + 1) (by omega) ρ x₀ ℓ r h c w N N₀ θ a₀ jb t τ C₀ δ M
      hℓ hr hℓr hrh hw hw1 hc hN₀ hN hθ hθ1 hm hmb hrough hjb hsmall hshift hsjb hM
      hcarr R hsym hlegal hκ hlo hhi n hsmooth
  have hcost := outcomeGlobalCost_integral_le H₀ q x₀ ℓ r h c N₀ M κ a₀ jb t τ w
    hℓ.le hr hrh hw hw1 v hv hvd hτ F hθ hθ1 (fun k => (R k).law)
    (fun _ _ _ => paperCoefficientLaw (d := d) (q + 1)) n hnr
  have hp := sharedLargeClusterEvent_real_probability_le F hθ hθ1 S x₀ r h hr.le (hr.trans_le hrh).le
    (fun k => (R k).law) (fun _ _ _ => paperCoefficientLaw (d := d) (q + 1)) n (q + 1)
  have hsmallTV : (P false).totalVariation (P true) ≤ 1 / 2 :=
    htv.trans ((add_le_add hp (Real.sqrt_le_sqrt hcost)).trans hbudget)
  have hsymTV : (P true).totalVariation (P false) = (P false).totalVariation (P true) := by
    unfold DensityLaw.totalVariation
    congr 2
    funext z
    exact abs_sub_comm _ _
  apply carrierComparison_minimax_lower F hθ hθ1 S x₀ r (fun k => (R k).law)
    (paperCoefficientLaw (q + 1)) (kernel true) (kernel false) n (models true) (models false)
    (fun _ => rfl) (fun _ => rfl) hκ.le (a₀ * t * jb) (mul_nonneg hshift hjb)
  · intro z
    exact roughOutcomeStatisticalModel_center true S (paperCoefficientAtoms (q + 1) ρ) z.2
      x₀ ℓ r h a₀ jb t z.1.2 (F z.1) hθ hθ1 (hlegal S true z.1.2 z.2)
      ((F z.1).designLegal hθ hθ1 hlo hhi S x₀ r)
  · intro z
    exact roughOutcomeStatisticalModel_center false S (paperCoefficientAtoms (q + 1) ρ) z.2
      x₀ ℓ r h a₀ jb t z.1.2 (F z.1) hθ hθ1 (hlegal S false z.1.2 z.2)
      ((F z.1).designLegal hθ hθ1 hlo hhi S x₀ r)
  · exact hsymTV.trans_le hsmallTV

end CausalLowerbound.PartC


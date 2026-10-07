import CausalLowerbound.PartC.GlobalPropensityHellinger
import CausalLowerbound.PartC.MixedStatisticalModels
import CausalLowerbound.CommonMarginalTesting

/-! Total variation for the actual degree-one model mixtures. The two
models use the constructed carrier and coefficient kernels, and the
conditional Hellinger bound is proved, rather than assumed. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]
  {α β γ : Regularity} {Lπ L₀ Lτ κ lower upper : ℝ}

theorem propensity_witness_model_totalVariation_le
    (H₀ : DiscreteLaw ℕ) (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ ja b t τ C₀ δ M : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hℓr : ℓ ≤ r) (hrh : r ≤ h) (hw : 0 < w) (hw1 : w ≤ 1)
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
    (hκ : 0 < κ)
    (hlo : lower ≤ (1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d))
    (hhi : (1 + θ) ^ (5 ^ Fintype.card d) / (1 - θ) ^ (5 ^ Fintype.card d) ≤ upper)
    (n : ℕ)
    (hsmooth : ∀ (T : Finset (d → ℤ)) (ξ : T → MomentGrid (CoefficientExponent d Q) (4 * Q)) x,
      |b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q T x₀ r x)| ≤ 1) :
    let S := activeBlocks (d := d) r h
    let F := fun z : (S → ℕ) × (activeBlocks (d := d) ℓ h → Bool) =>
      physicalCarrierProfile (ι := Fin Q) (D := 1) x₀ ℓ r h c w N N₀ θ
        hℓ hr hc hN₀ hN hmb hrough hθ (extendBlockSample S z.1) z.2
    let kernel := fun (side : Bool) (k : S) ζ m =>
      if side then paperCoefficientLaw Q else (R k).kernel ζ m
    let models := fun (side : Bool)
      (z : ((S → ℕ) × (activeBlocks (d := d) ℓ h → Bool)) ×
        (S → MomentGrid (CoefficientExponent d Q) (4 * Q))) =>
      roughPropensityStatisticalModel side S (paperCoefficientAtoms Q ρ) z.2 x₀ ℓ r h ja b t z.1.2
        (F z.1) hθ hθ1 (hlegal S side z.1.2 z.2) ((F z.1).designLegal hθ hθ1 hlo hhi S x₀ r)
    let μ := mixedCarrierDesign F hθ hθ1 S x₀ r (fun k => (R k).law)
      (fun _ _ _ => paperCoefficientLaw (d := d) Q) n
    let P := fun side => carrierComparisonDensity F hθ hθ1 S x₀ r (fun k => (R k).law)
      (paperCoefficientLaw Q) (kernel side) n (models side) hκ.le
    (P false).totalVariation (P true) ≤
      μ.real (sharedLargeClusterEvent n Q x₀ r h) +
        Real.sqrt (∫ x, propensityGlobalCost H₀ Q x₀ ℓ r h c N₀ M θ κ ja b t τ w x ∂μ) := by
  let S := activeBlocks (d := d) r h
  let F := fun z : (S → ℕ) × (activeBlocks (d := d) ℓ h → Bool) =>
    physicalCarrierProfile (ι := Fin Q) (D := 1) x₀ ℓ r h c w N N₀ θ
      hℓ hr hc hN₀ hN hmb hrough hθ (extendBlockSample S z.1) z.2
  let kernel := fun (side : Bool) (k : S) ζ m =>
    if side then paperCoefficientLaw Q else (R k).kernel ζ m
  let models := fun (side : Bool)
    (z : ((S → ℕ) × (activeBlocks (d := d) ℓ h → Bool)) ×
      (S → MomentGrid (CoefficientExponent d Q) (4 * Q))) =>
    roughPropensityStatisticalModel side S (paperCoefficientAtoms Q ρ) z.2 x₀ ℓ r h ja b t z.1.2
      (F z.1) hθ hθ1 (hlegal S side z.1.2 z.2) ((F z.1).designLegal hθ hθ1 hlo hhi S x₀ r)
  let μ := mixedCarrierDesign F hθ hθ1 S x₀ r (fun k => (R k).law)
    (fun _ _ _ => paperCoefficientLaw (d := d) Q) n
  letI := mixedCarrierDesign_probability F hθ hθ1 S x₀ r (fun k => (R k).law)
    (fun _ _ _ => paperCoefficientLaw (d := d) Q) n
  let P := fun side => carrierModelConditional F hθ hθ1 S x₀ r (fun k => (R k).law)
    (kernel side) n (models side) hκ.le
  have heq (side : Bool) (x : Fin n → d → ℝ) : P side x =
      propensityWitnessConditional Q ρ side S x₀ ℓ r h c w N N₀ θ ja b t τ
        hℓ hr hc hN₀ hN hθ hθ1 hmb hrough R (hlegal S side) hκ.le x :=
    (rawCarrierConditional_eq_model F hθ hθ1 S x₀ r (fun k => (R k).law)
      (kernel side) n (models side) hκ.le x).symm
  let cost := fun x : Fin n → d → ℝ => propensityGlobalCost H₀ Q x₀ ℓ r h c N₀ M θ κ ja b t τ w x
  have hi : Integrable cost μ := propensityGlobalCost_integrable H₀ Q x₀ ℓ r h c N₀ M κ ja b t τ w
    hr hrh hw hw1 F hθ hθ1 (fun k => (R k).law) (fun _ _ _ => paperCoefficientLaw (d := d) Q) n
  have hhell (x : Fin n → d → ℝ) (hx : x ∉ sharedLargeClusterEvent n Q x₀ r h) :
      (P false x).hellingerSq (P true x) ≤ cost x := by
    rw [heq, heq]
    exact propensity_witness_global_conditional_hellinger H₀ Q hQ ρ x₀ ℓ r h c w N N₀ θ ja b t τ C₀ δ M
      hℓ hr hℓr hrh hw hw1 hc hN₀ hN hθ hθ1 hm hmb hrough hja hsmall hb hb1 ht hbtja hM
      hcarr R hsym hlegal hκ n x hx (fun T ξ i => hsmooth T ξ (x i))
  have he := common_marginal_component_principle μ (P false) (P true)
    (carrierModelConditional_measurable F hθ hθ1 S x₀ r (fun k => (R k).law) (kernel false) n (models false) hκ.le)
    (carrierModelConditional_measurable F hθ hθ1 S x₀ r (fun k => (R k).law) (kernel true) n (models true) hκ.le)
    (sharedLargeClusterEvent n Q x₀ r h) (sharedLargeClusterEvent_measurable n Q x₀ r h) cost hi hhell
  apply he.trans
  apply add_le_add_left
  apply Real.sqrt_le_sqrt
  exact integral_mono (hi.indicator (sharedLargeClusterEvent_measurable n Q x₀ r h).compl) hi (fun x => by
    by_cases hx : x ∈ (sharedLargeClusterEvent n Q x₀ r h)ᶜ
    · simp only [Set.indicator_of_mem hx]; exact le_rfl
    · simp only [Set.indicator_of_not_mem hx]
      exact propensityGlobalCost_nonneg H₀ Q x₀ ℓ r h c N₀ M θ κ ja b t τ w hr x)

end CausalLowerbound.PartC

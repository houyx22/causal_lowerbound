import CausalLowerbound.PartC.UntaperedGhostMatching

/-! Cancel the empty observation pattern exactly. The remaining shared
resampled sum is the actual target-side likelihood increment, with the
same ghost carrier on both sides. Thus later comparison estimates need
only treat nonempty patterns and the target likelihood difference. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative MvPolynomial
variable {d I K : Type*} [Fintype d] [DecidableEq d]
  [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

theorem observationChoiceSet_none (k : K) : observationChoiceSet (fun _ : I => none) k = ∅ := by
  simp [observationChoiceSet]

theorem choiceBase_none (a : I → ℝ) : choiceBase a (fun _ : I => (none : Option K)) = ∏ i, a i := by
  simpa only [choiceValue, Option.elim_none, Finset.prod_const_one, mul_one] using
    (choiceValue_split a (fun (_ : I) (_ : K) => (1 : ℝ)) (fun _ => none)).symm

theorem choice_shift_product_none (δ : I → K → ℝ) :
    (∏ i : ShiftPositions (fun _ : I => (none : Option K)),
      δ i.val (choiceSite (fun _ => none) i)) = 1 := by
  apply Finset.prod_eq_one
  intro i _
  have hf : False := by simpa using i.property
  exact hf.elim

theorem nonempty_observation_choice_sum (F : (I → Option K) → ℝ) :
    (∑ s : I → Option K, if 0 < choiceDegree s then F s else 0) =
      (∑ s : I → Option K, F s) - F (fun _ => none) := by
  have he (s : I → Option K) : F s =
      (if 0 < choiceDegree s then F s else 0) + (if s = (fun _ => none) then F (fun _ => none) else 0) := by
    by_cases hs : s = (fun _ => none)
    · have hz := (choiceDegree_zero_iff s).2 hs
      rw [if_neg (by omega), if_pos hs, zero_add, hs]
    · have hp : 0 < choiceDegree s := Nat.pos_of_ne_zero (fun hz => hs ((choiceDegree_zero_iff s).1 hz))
      simp only [if_pos hp, if_neg hs, add_zero]
  have hsum : (∑ s : I → Option K, F s) =
      (∑ s : I → Option K, if 0 < choiceDegree s then F s else 0) + F (fun _ => none) := by
    calc
      _ = ∑ s : I → Option K, ((if 0 < choiceDegree s then F s else 0) +
          (if s = (fun _ => none) then F (fun _ => none) else 0)) := Finset.sum_congr rfl (fun s _ => he s)
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  linarith

theorem propensityObservationCoefficient_none (Q : ℕ) (ρ : ℝ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) :
    propensityObservationCoefficient Q ρ side S x₀ ℓ r h ja b t ζ x y ξ (fun _ => none) =
      ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i)) := by
  have hp := choice_shift_product_none (fun (i : I) (k : S) =>
    mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i) (y i) k.val 1)
  simp only [propensityObservationCoefficient, choiceBase_none, hp,
    (choiceDegree_zero_iff (fun _ : I => (none : Option S))).2 rfl, pow_zero, one_mul, mul_one]

theorem physical_untapered_ghost_increment_matching
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N N₀ ja b t : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hw : 0 < w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hja : ja ^ 2 ≤ 1)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (hmb : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) :
    let u₀ := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
      carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
    let W := fun (ζ η : activeBlocks (d := d) ℓ h → Bool) (k : S) (A : Finset (Fin Q)) =>
      ghostPatternIntegral x₀ ℓ r h k.val c w N ja (B k) (e k) (u₀ k)
        (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (u₀ k i)) η A (fun _ => 1)
    let cells := fun side ζ => ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      ∑ s : I → Option S, if 0 < choiceDegree s then
        propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s *
          ∏ k, W ζ η k ((observationChoiceSet s k).image (retainedObservationSlot Q hQ x₀ r k.val x (e k)))
        else 0) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      (∏ k, W ζ η k ∅) * (cells true ζ - cells false ζ)) ζ) := by
  let u₀ := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
    carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
  let W := fun (ζ η : activeBlocks (d := d) ℓ h → Bool) (k : S) (A : Finset (Fin Q)) =>
    ghostPatternIntegral x₀ ℓ r h k.val c w N ja (B k) (e k) (u₀ k)
      (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (u₀ k i)) η A (fun _ => 1)
  let cells := fun side ζ => ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
    (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))
  let U := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))
  let L := fun (ζ η : activeBlocks (d := d) ℓ h → Bool) (s : I → Option S) =>
    propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s *
      ∏ k, W ζ η k ((observationChoiceSet s k).image (retainedObservationSlot Q hQ x₀ r k.val x (e k)))
  let base := fun (ζ η : activeBlocks (d := d) ℓ h → Bool) => ∏ k, W ζ η k ∅
  have h0 (ζ η : activeBlocks (d := d) ℓ h → Bool) : L ζ η (fun _ => none) = base ζ η * cells false ζ := by
    simp only [L, propensityObservationCoefficient_none, observationChoiceSet_none, Finset.image_empty, base, cells]
    ring
  have hsum (ζ η : activeBlocks (d := d) ℓ h → Bool) :
      (∑ s : I → Option S, if 0 < choiceDegree s then L ζ η s else 0) =
        (∑ s, L ζ η s) - base ζ η * cells false ζ := by
    rw [nonempty_observation_choice_sum, h0]
  have he := physical_untapered_ghost_matching Q hQ ρ S x₀ ℓ r h c w N N₀ ja b t
    hℓ hr hh hw hw1 hc hN₀ hN hja hm hmb hrough x y hsep hcover htr B G e ξ
  change independentSigns.expect (fun ζ => Walsh.resampleAverage U (fun η => ∑ s, L ζ η s) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage U (fun η => base ζ η * cells true ζ) ζ) at he
  change independentSigns.expect (fun ζ => Walsh.resampleAverage U
    (fun η => ∑ s : I → Option S, if 0 < choiceDegree s then L ζ η s else 0) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage U (fun η => base ζ η * (cells true ζ - cells false ζ)) ζ)
  simp_rw [hsum, mul_sub, Walsh.resampleAverage, FiniteLaw.expect_sub]
  exact congrArg (fun z : ℝ => z - independentSigns.expect
    (fun ζ => Walsh.resampleAverage U (fun η => base ζ η * cells false ζ) ζ)) he

end CausalLowerbound.PartC

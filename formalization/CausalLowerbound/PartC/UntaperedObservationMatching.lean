import CausalLowerbound.PartC.PhysicalCompletedMatching
import CausalLowerbound.PartC.PhysicalPatternContinuity
import CausalLowerbound.PartC.PropensityObservationWeights

/-! Match the actual binary-cell observation coefficients after shared
resampling and removal of the selected tapers. The cell normalization and
the selected-slot normalization are included exactly. This identity is
pointwise in the ghost locations and in the baseline coefficient sample. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative RoughPropensity MvPolynomial
variable {d I K V J : Type*} [Fintype d] [DecidableEq d]
  [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

theorem observation_pattern_cell_scaling (q t N : ℝ) (a : I → ℝ) (δ : I → K → ℝ)
    (slot : K → I → V)
    (hslot : ∀ k i j, δ i k ≠ 0 → δ j k ≠ 0 → slot k i = slot k j → i = j)
    (κ : K → V → ℝ) (W : K → Array d V J 1) (u : K → V × d → ℝ)
    (z : K → V → ℝ) (η : J → Bool) (s : I → Option K) :
    (choiceBase (fun i => q * a i) s *
      (t ^ choiceDegree s * ∏ i : ShiftPositions s, q * δ i.val (choiceSite s i))) *
      propensityPatternProduct N κ W u z η (fun k => (observationChoiceSet s k).image (slot k)) =
    q ^ Fintype.card I * ((choiceBase a s * ∏ i : ShiftPositions s, (t * N) * δ i.val (choiceSite s i)) *
      ∏ k, propensityPatternWeight (κ k) (W k) (u k) (z k) η
        ((observationChoiceSet s k).image (slot k))) := by
  have hc := choice_rough_factorization (fun _ : I => q) a δ s
  simp only [Finset.prod_const, Finset.card_univ] at hc
  have hn := observation_pattern_normalization t N δ slot hslot κ W u z η s
  calc
    _ = t ^ choiceDegree s *
        (choiceBase (fun i => q * a i) s * ∏ i : ShiftPositions s, q * δ i.val (choiceSite s i)) *
          propensityPatternProduct N κ W u z η (fun k => (observationChoiceSet s k).image (slot k)) := by ring
    _ = q ^ Fintype.card I * (choiceBase a s *
        (t ^ choiceDegree s * (∏ i : ShiftPositions s, δ i.val (choiceSite s i)) *
          propensityPatternProduct N κ W u z η (fun k => (observationChoiceSet s k).image (slot k)))) := by
      rw [hc]
      ring
    _ = _ := by rw [← hn]; ring

theorem physical_untapered_observation_matching
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N ja b t : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hw : 0 < w) (hw1 : w ≤ 1) (hN : N ≠ 0)
    (hm : ∀ y : d → ℝ, assignmentMultiplier c w y * linearPartition y = assignmentPartition w y)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ghost : ∀ k, G k → d → ℝ)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) :
    let u₀ := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
      carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      ∑ s : I → Option S, propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s *
        ∏ k, partialPhysicalPatternWeight x₀ ℓ r h k.val c w N ja (B k) (e k) (u₀ k)
          (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (u₀ k i)) η
          ((observationChoiceSet s k).image (retainedObservationSlot Q hQ x₀ r k.val x (e k))) (ghost k)) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      (∏ k, partialPhysicalCarrierValue x₀ ℓ r h k.val c w N (B k) (e k) (u₀ k)
        (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (u₀ k i)) η (ghost k)) *
        ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
          (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ (x i) (y i))) ζ) := by
  let u₀ := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
    carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
  let u := fun k : S => completedConfiguration (e k) (u₀ k) (ghost k)
  let z := fun (ζ η : activeBlocks (d := d) ℓ h → Bool) (k : S) => completedSites (e k)
    (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (u₀ k i))
    (fun j => normalizedRoughChart x₀ ℓ r h k.val c w N η (ghost k j))
  let κ := fun k : S => physicalPropensitySlotCorrection x₀ r h k.val c w N ja (u k)
  let slot := fun k : S => retainedObservationSlot Q hQ x₀ r k.val x (e k)
  let U := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))
  let smooth := fun i => b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
    (globalCarriedPolynomial Q S x₀ r (x i))
  let L := fun (ζ : activeBlocks (d := d) ℓ h → Bool) i =>
    likelihood (sign (y i).1) (sign (y i).2) ja (smooth i) (physicalRoughField x₀ ℓ h ζ (x i))
  let Δ := fun (ζ : activeBlocks (d := d) ℓ h → Bool) i (k : S) =>
    increment (sign (y i).1) (sign (y i).2) ja (b * linearPartition (localCoordinate x₀ r k.val (x i)))
      (physicalRoughField x₀ ℓ h ζ (x i))
  let D := fun (ζ : activeBlocks (d := d) ℓ h → Bool) i (k : S) =>
    increment (sign (y i).1) (sign (y i).2) ja
      ((b * linearPartition (localCoordinate x₀ r k.val (x i))) * (t * N)) (physicalRoughField x₀ ℓ h ζ (x i))
  let F := fun (ζ : activeBlocks (d := d) ℓ h → Bool) i => L ζ i +
    realField (sign (y i).1) (sign (y i).2) ja (targetField x₀ h (ja * b * t) (x i))
      (physicalRoughField x₀ ℓ h ζ (x i))
  let A := fun (s : I → Option S) k => (observationChoiceSet s k).image (slot k)
  let C := fun (ζ η : activeBlocks (d := d) ℓ h → Bool) =>
    ∏ k, pointValue (torusProjection (u k)) (z ζ η k) η (B k)
  have hp (ζ : activeBlocks (d := d) ℓ h → Bool) (i : I) :
      eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (mixedPropensityCellPolynomial Q false S x₀ ℓ r h ja b t ζ (x i) (y i)) = (1 / 4) * L ζ i := by
    simp only [mixedPropensityCellPolynomial, map_mul, eval_C, propensitySitePolynomial_eval,
      Bool.false_eq_true, if_false, add_zero, L, smooth]
  have hp' (ζ : activeBlocks (d := d) ℓ h → Bool) (i : I) :
      eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ (x i) (y i)) = (1 / 4) * F ζ i := by
    simp only [mixedPropensityCellPolynomial, map_mul, eval_C, propensitySitePolynomial_eval,
      if_true, F, L, smooth]
  have hd (ζ : activeBlocks (d := d) ℓ h → Bool) (i : I) (k : S) :
      mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i) (y i) k.val 1 = (1 / 4) * Δ ζ i k := by
    simp only [mixedPropensityCellIncrement, Δ, increment]
    ring
  have hD (ζ : activeBlocks (d := d) ℓ h → Bool) (i : I) (k : S) : (t * N) * Δ ζ i k = D ζ i k := by
    simp only [Δ, D, increment]
    ring
  have hinc (ζ : activeBlocks (d := d) ℓ h → Bool) (i : I) (k : S) (hi : Δ ζ i k ≠ 0) :
      x i ∈ carrierBox x₀ r k.val := by
    apply linearPartition_nonzero_mem_carrierBox
    intro hz
    exact hi (by simp only [Δ, increment, hz, mul_zero, zero_mul])
  have hs (ζ : activeBlocks (d := d) ℓ h → Bool) (k : S) (i j : I)
      (hi : Δ ζ i k ≠ 0) (hj : Δ ζ j k ≠ 0) (he : slot k i = slot k j) : i = j :=
    retainedObservationSlot_injective_on_incident Q hQ x₀ r k.val x (e k) i j
      (hinc ζ i k hi) (hinc ζ j k hj) he
  have hleft (ζ η : activeBlocks (d := d) ℓ h → Bool) :
      (∑ s : I → Option S, propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s *
        propensityPatternProduct N κ B u (z ζ η) η (A s)) =
      (1 / 4 : ℝ) ^ Fintype.card I * ∑ s : I → Option S,
        (choiceBase (L ζ) s * ∏ i : ShiftPositions s, D ζ i.val (choiceSite s i)) *
          ∏ k, propensityPatternWeight (κ k) (B k) (u k) (z ζ η k) η (A s k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    unfold propensityObservationCoefficient
    simp only [hp, hd]
    simpa only [hD] using observation_pattern_cell_scaling (1 / 4) t N (L ζ) (Δ ζ)
      slot (hs ζ) κ B u (z ζ η) η s
  have hright (ζ η : activeBlocks (d := d) ℓ h → Bool) :
      C ζ η * (∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ (x i) (y i))) =
      (1 / 4 : ℝ) ^ Fintype.card I * (C ζ η * ∏ i, F ζ i) := by
    simp only [hp', Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    ring
  have he := physical_completed_shared_pattern_matching Q hQ S x₀ ℓ r h c w N ja b t
    hℓ hr hh hw hw1 hN hm x (fun i => sign (y i).1) (fun i => sign (y i).2) smooth
    hsep hcover htr B G e ghost
  change independentSigns.expect (fun ζ => Walsh.resampleAverage U (fun η =>
    ∑ s : I → Option S, (choiceBase (L ζ) s * ∏ i : ShiftPositions s, D ζ i.val (choiceSite s i)) *
      ∏ k, propensityPatternWeight (κ k) (B k) (u k) (z ζ η k) η (A s k)) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage U (fun η => C ζ η * ∏ i, F ζ i) ζ) at he
  change independentSigns.expect (fun ζ => Walsh.resampleAverage U (fun η =>
    ∑ s : I → Option S, propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s *
      propensityPatternProduct N κ B u (z ζ η) η (A s)) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage U (fun η => C ζ η *
      ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ (x i) (y i))) ζ)
  simp_rw [hleft, hright, Walsh.resampleAverage, FiniteLaw.expect_mul]
  exact congrArg (fun z : ℝ => (1 / 4 : ℝ) ^ Fintype.card I * z) he

end CausalLowerbound.PartC

import CausalLowerbound.PartC.GlobalPropensityShift
import CausalLowerbound.PartC.ObservationBlockChoices
import CausalLowerbound.PartC.RetainedObservationSlots
import CausalLowerbound.PartC.TaperedSiteFunctional

/-! Exact block-pattern expansion of the actual propensity component
polynomial. Completed physical configurations supply every interpolation
slot. Taper-zero blocks are handled by the proved amplitude mask. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry ConfigurationShells MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I Ω : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I] [Fintype Ω]

theorem block_shift_observation_expansion {K A V : Type*}
    [Fintype K] [DecidableEq K] [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
    (μ : K → FiniteLaw Ω) (U : K → Ω → A → ℝ) (c : K → A → V → ℝ) (amp : K → ℝ)
    (w : K → Finset V → ℝ) (p : MvPolynomial (K × A) ℝ)
    (base : (K → Ω) → I → ℝ) (δ : I → K → ℝ) (slot : K → I → V)
    (hshift : blockShiftAverage μ U c amp p = ∑ ξ : K → Ω,
      C ((FiniteLaw.independent μ).weight ξ) *
        ∏ i, (C (base ξ i) + ∑ k, C (δ i k) * X (k, slot k i)))
    (hslot : ∀ k i j, δ i k ≠ 0 → δ j k ≠ 0 → slot k i = slot k j → i = j) :
    blockPolynomialFunctional (fun k => (sitePatternFunctional (w k)).comp
      (coefficientShiftAverage (μ k) (U k) (c k) (amp k))) p =
      (FiniteLaw.independent μ).expect (fun ξ => ∑ s : I → Option K,
        (choiceBase (base ξ) s * ∏ i : ShiftPositions s, δ i.val (choiceSite s i)) *
          ∏ k, w k ((observationChoiceSet s k).image (slot k))) := by
  rw [blockPolynomialFunctional_shift_average, hshift, map_sum]
  simp only [MvPolynomial.C_mul', map_smul, smul_eq_mul, FiniteLaw.expect]
  apply Finset.sum_congr rfl
  intro ξ _
  simpa only [MvPolynomial.C_mul'] using
    congrArg (fun a : ℝ => (FiniteLaw.independent μ).weight ξ * a)
      (block_site_observation_expansion w (base ξ) δ slot hslot)

theorem mixedPropensityComponentPolynomial_pattern_expansion (Q : ℕ) (hQ : 0 < Q)
    (side : Bool) (S : Finset (d → ℤ)) (μ : S → FiniteLaw Ω)
    (U : S → Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h ja b t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (u : S → Fin Q × d → ℝ) (amp : S → ℝ) (τ : ℝ) (slot : S → I → Fin Q)
    (hkeep : ∀ k i, linearPartition (localCoordinate x₀ r k.val (x i)) ≠ 0 →
      configurationSite (u k) (slot k i) = carrierCoordinate (localCoordinate x₀ r k.val (x i)))
    (hslot : ∀ k i j, linearPartition (localCoordinate x₀ r k.val (x i)) ≠ 0 →
      linearPartition (localCoordinate x₀ r k.val (x j)) ≠ 0 → slot k i = slot k j → i = j)
    (hχ : ∀ k, amp k ≠ 0 →
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight (u k)) ≠ 0)
    (w : S → Finset (Fin Q) → ℝ) :
    blockPolynomialFunctional (fun k => (sitePatternFunctional (w k)).comp
      (coefficientShiftAverage (μ k) (U k)
        (fun a v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree a) (u k)) (amp k)))
      (mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y) =
      (FiniteLaw.independent μ).expect (fun ξ => ∑ s : I → Option S,
        (choiceBase (fun i => eval (fun ka => U ka.1 (ξ ka.1) ka.2)
          (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))) s *
            ∏ i : ShiftPositions s, mixedPropensityCellIncrement x₀ ℓ r h ja b ζ
              (x i.val) (y i.val) (choiceSite s i).val (amp (choiceSite s i))) *
          ∏ k : S, w k ((observationChoiceSet s k).image (slot k))) := by
  have hδ : ∀ (k : S) (i j : I),
      mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i) (y i) k.val (amp k) ≠ 0 →
      mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x j) (y j) k.val (amp k) ≠ 0 →
      slot k i = slot k j → i = j := by
    intro k i j hi hj hij
    apply hslot k i j _ _ hij
    · intro hz
      exact hi (by simp only [mixedPropensityCellIncrement, hz, mul_zero, zero_mul])
    · intro hz
      exact hj (by simp only [mixedPropensityCellIncrement, hz, mul_zero, zero_mul])
  have hshift := mixedPropensityComponentPolynomial_shift_average Q hQ side S μ U x₀ ℓ r h ja b t ζ x y
    u amp τ slot hkeep hχ
  have he := block_shift_observation_expansion (I := I) (Ω := Ω) (K := S)
    (A := CoefficientExponent d Q) (V := Fin Q) μ U
    (fun k a v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree (d := d) (Q := Q) a) (u k)) amp w
    (mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y)
    (fun ξ i => eval (fun ka => U ka.1 (ξ ka.1) ka.2)
      (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i)))
    (fun i k => mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i) (y i) k.val (amp k)) slot
    (by exact hshift) hδ
  exact he

theorem completed_propensity_pattern_expansion (Q : ℕ) (hQ : 0 < Q)
    (side : Bool) (S : Finset (d → ℤ)) (μ : S → FiniteLaw Ω)
    (U : S → Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h ja b t τ : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ghost : ∀ k, G k → d → ℝ) (amp : S → ℝ) (w : S → Finset (Fin Q) → ℝ) :
    let u := fun k : S => completedConfiguration (e k)
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)
    let slot := fun k : S => retainedObservationSlot Q hQ x₀ r k.val x (e k)
    let χ := fun k => graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight (u k))
    let amp' := fun k => if χ k = 0 then 0 else amp k
    blockPolynomialFunctional (fun k => (sitePatternFunctional (taperedPatternWeight (χ k) (w k))).comp
      (coefficientShiftAverage (μ k) (U k)
        (fun a v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree a) (u k)) (amp k)))
      (mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y) =
      (FiniteLaw.independent μ).expect (fun ξ => ∑ s : I → Option S,
        (choiceBase (fun i => eval (fun ka => U ka.1 (ξ ka.1) ka.2)
          (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))) s *
            ∏ i : ShiftPositions s, mixedPropensityCellIncrement x₀ ℓ r h ja b ζ
              (x i.val) (y i.val) (choiceSite s i).val (amp' (choiceSite s i))) *
          ∏ k : S, taperedPatternWeight (χ k) (w k) ((observationChoiceSet s k).image (slot k))) := by
  dsimp only
  let u := fun k : S => completedConfiguration (e k)
    (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)
  let χ := fun k => graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight (u k))
  let amp' := fun k => if χ k = 0 then 0 else amp k
  have hmaps : (fun k : S => (sitePatternFunctional (taperedPatternWeight (χ k) (w k))).comp
      (coefficientShiftAverage (μ k) (U k)
        (fun a v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree a) (u k)) (amp k))) =
      (fun k : S => (sitePatternFunctional (taperedPatternWeight (χ k) (w k))).comp
        (coefficientShiftAverage (μ k) (U k)
          (fun a v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree a) (u k)) (amp' k))) := by
    funext k
    apply LinearMap.ext
    intro p
    exact taperedSiteFunctional_mask_amplitude (μ k) (U k) _ (amp k) (χ k) (w k) p
  rw [hmaps]
  apply mixedPropensityComponentPolynomial_pattern_expansion Q hQ side S μ U x₀ ℓ r h ja b t ζ x y
    u amp' τ (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k))
  · intro k i hi
    exact retainedObservationSlot_configuration Q hQ x₀ r k.val x (e k) (ghost k) i hi
  · intro k i j hi hj hij
    exact retainedObservationSlot_injective_on_incident Q hQ x₀ r k.val x (e k) i j
      (linearPartition_nonzero_mem_carrierBox x₀ r k.val (x i) hi)
      (linearPartition_nonzero_mem_carrierBox x₀ r k.val (x j) hj) hij
  · intro k hk hz
    exact hk (if_pos hz)

end CausalLowerbound.PartC

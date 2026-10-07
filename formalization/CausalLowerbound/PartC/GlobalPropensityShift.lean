import CausalLowerbound.PartC.BlockCoefficientShift
import CausalLowerbound.PartC.MixedLikelihoodPolynomials
import CausalLowerbound.PartB.RetainedEvaluation

/-! The simultaneous virtual shift of the actual global propensity
likelihood is affine at each observation. A zero amplitude needs no
separation hypothesis, so blocks with zero taper can be switched off. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry ConfigurationShells MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I Ω : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype Ω]

theorem globalCarriedPolynomial_eval_coefficients (Q : ℕ) (S : Finset (d → ℤ))
    (U : S → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) :
    eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r x) =
      ∑ k : S, linearPartition (localCoordinate x₀ r k.val x) *
        coefficientEvaluation (U k) (carrierCoordinate (localCoordinate x₀ r k.val x)) := by
  simp only [globalCarriedPolynomial, map_sum, map_mul, eval_C, eval_X,
    coefficientEvaluation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem globalCarriedPolynomial_shift_eval (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ))
    (U : S → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ)
    (u : S → Fin Q × d → ℝ) (amp : S → ℝ) (τ : ℝ) (keep : S → Fin Q)
    (hkeep : ∀ k, linearPartition (localCoordinate x₀ r k.val x) ≠ 0 →
      configurationSite (u k) (keep k) = carrierCoordinate (localCoordinate x₀ r k.val x))
    (hχ : ∀ k, amp k ≠ 0 →
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight (u k)) ≠ 0)
    (z : S × Fin Q → ℝ) :
    eval (fun ka => U ka.1 ka.2 + ∑ v, amp ka.1 *
        lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree ka.2) (u ka.1) * z (ka.1, v))
      (globalCarriedPolynomial Q S x₀ r x) =
      eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r x) +
        ∑ k : S, linearPartition (localCoordinate x₀ r k.val x) * amp k * z (k, keep k) := by
  rw [globalCarriedPolynomial_eval_coefficients Q S (fun k a => U k a + ∑ v, amp k *
      lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree a) (u k) * z (k, v)) x₀ r x,
    globalCarriedPolynomial_eval_coefficients Q S U x₀ r x,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases ha : amp k = 0
  · simp only [ha, zero_mul, Finset.sum_const_zero, add_zero, mul_zero]
  by_cases hp : linearPartition (localCoordinate x₀ r k.val x) = 0
  · simp only [hp, zero_mul, add_zero]
  have hs : (fun a => U k a + ∑ v, amp k *
      lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree a) (u k) * z (k, v)) =
      virtualCoefficientShift (U k) (u k) (amp k) (fun v => z (k, v)) := by
    funext a
    simp only [virtualCoefficientShift, Finset.mul_sum, mul_assoc]
  rw [hs, ← hkeep k hp, virtualCoefficientShift_evaluation Q hQ (by simp) (U k) (u k)
    (taper_nonzero_chord_ne_zero (u k) τ (hχ k ha))]
  ring

def mixedPropensityCellIncrement (x₀ : d → ℝ) (ℓ r h ja b : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ) (y : Bool × Bool)
    (k : d → ℤ) (amp : ℝ) : ℝ :=
  (1 / 4) * (1 + sign y.1 * ja * physicalRoughField x₀ ℓ h ζ x) * sign y.2 * b *
    linearPartition (localCoordinate x₀ r k x) * amp

theorem mixedPropensityCellPolynomial_shift_eval (Q : ℕ) (hQ : 0 < Q)
    (side : Bool) (S : Finset (d → ℤ)) (U : S → CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : d → ℝ) (y : Bool × Bool) (u : S → Fin Q × d → ℝ) (amp : S → ℝ)
    (τ : ℝ) (keep : S → Fin Q)
    (hkeep : ∀ k, linearPartition (localCoordinate x₀ r k.val x) ≠ 0 →
      configurationSite (u k) (keep k) = carrierCoordinate (localCoordinate x₀ r k.val x))
    (hχ : ∀ k, amp k ≠ 0 →
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight (u k)) ≠ 0)
    (z : S × Fin Q → ℝ) :
    eval (fun ka => U ka.1 ka.2 + ∑ v, amp ka.1 *
        lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree ka.2) (u ka.1) * z (ka.1, v))
      (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ x y) =
      eval (fun ka => U ka.1 ka.2) (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ x y) +
        ∑ k : S, mixedPropensityCellIncrement x₀ ℓ r h ja b ζ x y k.val (amp k) * z (k, keep k) := by
  have he : (∑ k : S, mixedPropensityCellIncrement x₀ ℓ r h ja b ζ x y k.val (amp k) * z (k, keep k)) =
      ((1 / 4) * (1 + sign y.1 * ja * physicalRoughField x₀ ℓ h ζ x) * sign y.2 * b) *
        ∑ k : S, linearPartition (localCoordinate x₀ r k.val x) * amp k * z (k, keep k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    unfold mixedPropensityCellIncrement
    ring
  rw [he]
  simp only [mixedPropensityCellPolynomial, map_mul, eval_C, propensitySitePolynomial_eval]
  rw [globalCarriedPolynomial_shift_eval Q hQ S U x₀ r x u amp τ keep hkeep hχ]
  unfold RoughPropensity.likelihood
  ring

theorem mixedPropensityComponentPolynomial_shift_average (Q : ℕ) (hQ : 0 < Q)
    (side : Bool) (S : Finset (d → ℤ)) (μ : S → FiniteLaw Ω)
    (U : S → Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h ja b t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (u : S → Fin Q × d → ℝ) (amp : S → ℝ) (τ : ℝ) (slot : S → I → Fin Q)
    (hkeep : ∀ k i, linearPartition (localCoordinate x₀ r k.val (x i)) ≠ 0 →
      configurationSite (u k) (slot k i) = carrierCoordinate (localCoordinate x₀ r k.val (x i)))
    (hχ : ∀ k, amp k ≠ 0 →
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight (u k)) ≠ 0) :
    blockShiftAverage μ U
      (fun k a v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree a) (u k)) amp
      (mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y) =
      ∑ ξ : S → Ω, C ((FiniteLaw.independent μ).weight ξ) * ∏ i,
        (C (eval (fun ka => U ka.1 (ξ ka.1) ka.2)
          (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))) +
            ∑ k : S, C (mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i) (y i) k.val (amp k)) *
              X (k, slot k i)) := by
  apply MvPolynomial.funext
  intro z
  rw [blockShiftAverage_eval]
  simp only [map_sum, map_mul, map_prod, map_add, eval_C, eval_X]
  change (FiniteLaw.independent μ).expect _ = (FiniteLaw.independent μ).expect _
  apply FiniteLaw.expect_congr
  intro ξ
  rw [mixedPropensityComponentPolynomial, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact mixedPropensityCellPolynomial_shift_eval Q hQ side S (fun k => U k (ξ k))
    x₀ ℓ r h ja b t ζ (x i) (y i) u amp τ (fun k => slot k i) (fun k => hkeep k i) hχ z

end CausalLowerbound.PartC

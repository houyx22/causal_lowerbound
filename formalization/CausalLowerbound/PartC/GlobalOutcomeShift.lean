import CausalLowerbound.PartC.GlobalPropensityShift
import CausalLowerbound.PartC.OutcomeLikelihoodPolynomials

/-! The simultaneous coefficient shift of the actual rough-outcome
likelihood is the full cubic Taylor polynomial in all incident blocks.
No mixed block terms are omitted. Zero amplitudes need no separation. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry ConfigurationShells MvPolynomial RoughOutcome
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I Ω : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype Ω]

theorem mixedOutcomeCellPolynomial_shift_taylor (Q : ℕ) (hQ : 0 < Q)
    (S : Finset (d → ℤ)) (U : S → CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : d → ℝ) (y : Bool × Bool) (u : S → Fin Q × d → ℝ) (amp : S → ℝ)
    (τ : ℝ) (keep : S → Fin Q)
    (hkeep : ∀ k, linearPartition (localCoordinate x₀ r k.val x) ≠ 0 →
      configurationSite (u k) (keep k) = carrierCoordinate (localCoordinate x₀ r k.val x))
    (hχ : ∀ k, amp k ≠ 0 →
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight (u k)) ≠ 0)
    (z : S × Fin Q → ℝ) :
    eval (fun ka => U ka.1 ka.2 + ∑ v, amp ka.1 *
        lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree ka.2) (u ka.1) * z (ka.1, v))
      (mixedOutcomeCellPolynomial Q false S x₀ ℓ r h a jb t ζ x y) =
    eval z (C (1 / 4) * outcomeTaylorPolynomial (sign y.1) (sign y.2) 1 jb
      (physicalRoughCorrection x₀ ℓ h (a * t) x)
      (a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r x))
      (physicalRoughField x₀ ℓ h ζ x)
      (∑ k : S, C (a * linearPartition (localCoordinate x₀ r k.val x) * amp k) * X (k, keep k))) := by
  simp only [mixedOutcomeCellPolynomial, map_mul, eval_C, outcomeSitePolynomial_eval,
    Bool.false_eq_true, if_false, add_zero, outcomeTaylorPolynomial_eval,
    map_sum, eval_X, one_mul]
  rw [globalCarriedPolynomial_shift_eval Q hQ S U x₀ r x u amp τ keep hkeep hχ]
  have he : a * (eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r x) +
      ∑ k : S, linearPartition (localCoordinate x₀ r k.val x) * amp k * z (k, keep k)) =
      a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r x) +
        ∑ k : S, a * linearPartition (localCoordinate x₀ r k.val x) * amp k * z (k, keep k) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he]

theorem mixedOutcomeComponentPolynomial_shift_average (Q : ℕ) (hQ : 0 < Q)
    (S : Finset (d → ℤ)) (μ : S → FiniteLaw Ω)
    (U : S → Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h a jb t : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (u : S → Fin Q × d → ℝ) (amp : S → ℝ) (τ : ℝ) (slot : S → I → Fin Q)
    (hkeep : ∀ k i, linearPartition (localCoordinate x₀ r k.val (x i)) ≠ 0 →
      configurationSite (u k) (slot k i) = carrierCoordinate (localCoordinate x₀ r k.val (x i)))
    (hχ : ∀ k, amp k ≠ 0 →
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight (u k)) ≠ 0) :
    blockShiftAverage μ U
      (fun k a v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree a) (u k)) amp
      (mixedOutcomeComponentPolynomial Q false S x₀ ℓ r h a jb t ζ x y) =
      ∑ ξ : S → Ω, C ((FiniteLaw.independent μ).weight ξ) * ∏ i,
        (C (1 / 4) * outcomeTaylorPolynomial (sign (y i).1) (sign (y i).2) 1 jb
          (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
          (a * eval (fun ka => U ka.1 (ξ ka.1) ka.2) (globalCarriedPolynomial Q S x₀ r (x i)))
          (physicalRoughField x₀ ℓ h ζ (x i))
          (∑ k : S, C (a * linearPartition (localCoordinate x₀ r k.val (x i)) * amp k) * X (k, slot k i))) := by
  apply MvPolynomial.funext
  intro z
  rw [blockShiftAverage_eval]
  simp only [map_sum, map_mul, map_prod, eval_C]
  change (FiniteLaw.independent μ).expect _ = (FiniteLaw.independent μ).expect _
  apply FiniteLaw.expect_congr
  intro ξ
  rw [mixedOutcomeComponentPolynomial, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [map_mul, eval_C] using mixedOutcomeCellPolynomial_shift_taylor Q hQ S (fun k => U k (ξ k))
    x₀ ℓ r h a jb t ζ (x i) (y i) u amp τ (fun k => slot k i) (fun k => hkeep k i) hχ z

end CausalLowerbound.PartC

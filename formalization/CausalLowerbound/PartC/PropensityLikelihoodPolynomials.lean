import CausalLowerbound.PartC.PhysicalPropensityPolynomial
import CausalLowerbound.PartC.SingleSiteBridge
import CausalLowerbound.PartB.LikelihoodPolynomials
import CausalLowerbound.PartB.RetainedEvaluation

/-! Actual rough-propensity likelihoods as coefficient polynomials. On
the nonzero taper region their virtual coefficient shift becomes an
affine product at the retained slots, for any retained/ghost split. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial PartB PartB.ShellGeometry ConfigurationShells RoughPropensity
variable {A I d V Ω : Type*} [Fintype A] [Fintype I]
  [Fintype d] [DecidableEq d] [Fintype V] [LinearOrder V] [Fintype Ω]

def propensityCellPolynomial (R T ja rough : ℝ) (smooth : MvPolynomial A ℝ) : MvPolynomial A ℝ :=
  C (1 + R * ja * rough) * (1 + C T * smooth)

theorem propensityCellPolynomial_eval (R T ja rough : ℝ) (smooth : MvPolynomial A ℝ)
    (U : A → ℝ) :
    eval U (propensityCellPolynomial R T ja rough smooth) = likelihood R T ja (eval U smooth) rough := by
  simp only [propensityCellPolynomial, map_mul, map_add, map_one, eval_C, likelihood]

theorem propensityCellPolynomial_degree (R T ja rough : ℝ) (smooth : MvPolynomial A ℝ)
    (hs : smooth.totalDegree ≤ 1) :
    (propensityCellPolynomial R T ja rough smooth).totalDegree ≤ 1 := by
  apply (polynomial_const_mul_degree _ _).trans
  exact (totalDegree_add _ _).trans
    (max_le (by simp) ((polynomial_const_mul_degree _ _).trans hs))

def retainedPropensityPolynomial (Q : ℕ) (R T ja rough offset ψ : I → ℝ) (sites : I → d → ℝ) :
    MvPolynomial (CoefficientExponent d Q) ℝ :=
  ∏ i, propensityCellPolynomial (R i) (T i) (ja i) (rough i)
    (retainedFieldPolynomial Q (offset i) (ψ i) (sites i))

theorem retainedPropensityPolynomial_eval (Q : ℕ) (R T ja rough offset ψ : I → ℝ)
    (sites : I → d → ℝ) (U : CoefficientExponent d Q → ℝ) :
    eval U (retainedPropensityPolynomial Q R T ja rough offset ψ sites) =
      ∏ i, likelihood (R i) (T i) (ja i) (offset i + ψ i * coefficientEvaluation U (sites i)) (rough i) := by
  simp only [retainedPropensityPolynomial, map_prod, propensityCellPolynomial_eval, retainedFieldPolynomial_eval]

theorem retainedPropensityPolynomial_degree (Q : ℕ) (R T ja rough offset ψ : I → ℝ)
    (sites : I → d → ℝ) :
    (retainedPropensityPolynomial Q R T ja rough offset ψ sites).totalDegree ≤ Fintype.card I := by
  apply (totalDegree_finset_prod _ _).trans
  calc
    _ ≤ ∑ _i : I, 1 := Finset.sum_le_sum (fun i _ => propensityCellPolynomial_degree _ _ _ _ _
      (retainedFieldPolynomial_degree Q (offset i) (ψ i) (sites i)))
    _ = _ := by simp

theorem coefficientShiftPolynomial_retained_propensity (Q : ℕ) (hQ : 0 < Q)
    (hcard : Fintype.card V ≤ Q) (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (u : V × d → ℝ) (τ amp : ℝ) (keep : I → V) (sites : I → d → ℝ)
    (hkeep : ∀ i, configurationSite u (keep i) = sites i)
    (R T ja rough offset ψ : I → ℝ)
    (hχ : graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) ≠ 0) :
    coefficientShiftPolynomial μ U (fun e i => lagrangeCoefficient edgeLeft edgeRight i (polynomialBasisDegree e) u) amp
      (retainedPropensityPolynomial Q R T ja rough offset ψ sites) =
      (∑ ω, C (μ.weight ω) * ∏ i,
        (C (increment (R i) (T i) (ja i) (ψ i * amp) (rough i)) * X (keep i) +
          C (likelihood (R i) (T i) (ja i)
            (offset i + ψ i * coefficientEvaluation (U ω) (sites i)) (rough i)))) -
        C (μ.expect (fun ω => ∏ i, likelihood (R i) (T i) (ja i)
          (offset i + ψ i * coefficientEvaluation (U ω) (sites i)) (rough i))) := by
  apply MvPolynomial.funext
  intro z
  rw [coefficientShiftPolynomial_eval]
  simp only [map_sub, map_sum, map_mul, map_prod, map_add, eval_C, eval_X,
    retainedPropensityPolynomial_eval]
  apply congrArg₂ (fun x y : ℝ => x - y) _ rfl
  apply μ.expect_congr
  intro ω
  have hs : (fun e => U ω e + ∑ i, amp * lagrangeCoefficient edgeLeft edgeRight i (polynomialBasisDegree e) u * z i) =
      virtualCoefficientShift (U ω) u amp z := by
    funext e
    simp only [virtualCoefficientShift, Finset.mul_sum, mul_assoc]
  rw [hs]
  apply Finset.prod_congr rfl
  intro i _
  rw [← hkeep i, virtualCoefficientShift_evaluation Q hQ hcard (U ω) u
    (taper_nonzero_chord_ne_zero u τ hχ)]
  unfold likelihood increment
  ring

theorem propensityCoefficientFunctional_retained {J : Type*} [Fintype J] [DecidableEq J]
    (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (u : V × d → ℝ) (τ amp : ℝ) (keep : I → V) (sites : I → d → ℝ)
    (hkeep : ∀ i, configurationSite u (keep i) = sites i)
    (R T ja rough offset ψ : I → ℝ) (κ : V → ℝ)
    (W : Representative.Array d V J 1) (z : V → ℝ) (ζ : J → Bool) :
    propensityCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ κ W u z ζ
      (retainedPropensityPolynomial Q R T ja rough offset ψ sites) =
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) *
        (μ.expect (fun ω => propensityPolynomialFunctional κ W u z ζ
          (∏ i, (C (increment (R i) (T i) (ja i) (ψ i * amp) (rough i)) * X (keep i) +
            C (likelihood (R i) (T i) (ja i)
              (offset i + ψ i * coefficientEvaluation (U ω) (sites i)) (rough i))))) -
          μ.expect (fun ω => ∏ i, likelihood (R i) (T i) (ja i)
            (offset i + ψ i * coefficientEvaluation (U ω) (sites i)) (rough i)) *
              Representative.pointValue (Wiener.torusProjection u) z ζ W) := by
  rw [propensityCoefficientFunctional, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
  by_cases hχ : graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) = 0
  · simp only [hχ, zero_mul]
  · rw [coefficientShiftPolynomial_retained_propensity Q hQ hcard μ U u τ amp keep sites hkeep
      R T ja rough offset ψ hχ, map_sub, map_sum]
    simp only [MvPolynomial.C_mul', map_smul, smul_eq_mul, propensityPolynomialFunctional_C]
    rfl

end CausalLowerbound.PartC

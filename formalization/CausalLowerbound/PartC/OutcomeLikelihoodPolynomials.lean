import CausalLowerbound.PartC.PhysicalOutcomePolynomial
import CausalLowerbound.PartC.MixedLikelihoodPolynomials
import CausalLowerbound.PartB.RetainedEvaluation

/-! The actual cubic outcome likelihood as a coefficient polynomial.
On the nonzero taper region, virtual interpolation gives the exact cubic
Taylor polynomial at every retained site, with the rough field fixed. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial PartB PartB.ShellGeometry ConfigurationShells RoughOutcome
variable {A I d V Ω : Type*} [Fintype A] [Fintype I]
  [Fintype d] [DecidableEq d] [Fintype V] [LinearOrder V] [Fintype Ω]

def outcomeCellPolynomial (R T jb η rough : ℝ) (smooth : MvPolynomial A ℝ) : MvPolynomial A ℝ :=
  outcomeSitePolynomial false R T 1 jb η 0 rough smooth

theorem outcomeCellPolynomial_eval (R T jb η rough : ℝ) (smooth : MvPolynomial A ℝ)
    (U : A → ℝ) :
    eval U (outcomeCellPolynomial R T jb η rough smooth) = likelihood R T jb η (eval U smooth) rough := by
  simp only [outcomeCellPolynomial, outcomeSitePolynomial_eval, one_mul, Bool.false_eq_true, if_false, add_zero]

theorem outcomeCellPolynomial_degree (R T jb η rough : ℝ) (smooth : MvPolynomial A ℝ)
    (hs : smooth.totalDegree ≤ 1) :
    (outcomeCellPolynomial R T jb η rough smooth).totalDegree ≤ 3 :=
  outcomeSitePolynomial_degree false R T 1 jb η 0 rough smooth hs

def retainedOutcomePolynomial (Q : ℕ) (R T jb η rough offset ψ : I → ℝ) (sites : I → d → ℝ) :
    MvPolynomial (CoefficientExponent d Q) ℝ :=
  ∏ i, outcomeCellPolynomial (R i) (T i) (jb i) (η i) (rough i)
    (retainedFieldPolynomial Q (offset i) (ψ i) (sites i))

theorem retainedOutcomePolynomial_eval (Q : ℕ) (R T jb η rough offset ψ : I → ℝ)
    (sites : I → d → ℝ) (U : CoefficientExponent d Q → ℝ) :
    eval U (retainedOutcomePolynomial Q R T jb η rough offset ψ sites) =
      ∏ i, likelihood (R i) (T i) (jb i) (η i) (offset i + ψ i * coefficientEvaluation U (sites i)) (rough i) := by
  simp only [retainedOutcomePolynomial, map_prod, outcomeCellPolynomial_eval, retainedFieldPolynomial_eval]

theorem retainedOutcomePolynomial_degree (Q : ℕ) (R T jb η rough offset ψ : I → ℝ)
    (sites : I → d → ℝ) :
    (retainedOutcomePolynomial Q R T jb η rough offset ψ sites).totalDegree ≤ 3 * Fintype.card I := by
  apply (totalDegree_finset_prod _ _).trans
  calc
    _ ≤ ∑ _i : I, 3 := Finset.sum_le_sum (fun i _ => outcomeCellPolynomial_degree _ _ _ _ _ _
      (retainedFieldPolynomial_degree Q (offset i) (ψ i) (sites i)))
    _ = _ := by simp [mul_comm]

def outcomeTaylorPolynomial (R T shift jb η smooth rough : ℝ) (z : MvPolynomial V ℝ) : MvPolynomial V ℝ :=
  C (likelihood R T jb η smooth rough) + C (incrementOne R T shift jb η smooth rough) * z +
    C (incrementTwo R T shift jb smooth rough) * z ^ 2 + C (incrementThree R T shift jb rough) * z ^ 3

omit [Fintype V] [LinearOrder V] in
theorem outcomeTaylorPolynomial_eval (R T shift jb η smooth rough : ℝ)
    (p : MvPolynomial V ℝ) (z : V → ℝ) :
    eval z (outcomeTaylorPolynomial R T shift jb η smooth rough p) =
      likelihood R T jb η (smooth + shift * eval z p) rough := by
  simp only [outcomeTaylorPolynomial, map_add, map_mul, map_pow, eval_C]
  unfold likelihood outcome incrementOne incrementTwo incrementThree
  ring

theorem coefficientShiftPolynomial_retained_outcome (Q : ℕ) (hQ : 0 < Q)
    (hcard : Fintype.card V ≤ Q) (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (u : V × d → ℝ) (τ amp : ℝ) (keep : I → V) (sites : I → d → ℝ)
    (hkeep : ∀ i, configurationSite u (keep i) = sites i)
    (R T jb η rough offset ψ : I → ℝ)
    (hχ : graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) ≠ 0) :
    coefficientShiftPolynomial μ U (fun e i => lagrangeCoefficient edgeLeft edgeRight i (polynomialBasisDegree e) u) amp
      (retainedOutcomePolynomial Q R T jb η rough offset ψ sites) =
      (∑ ω, C (μ.weight ω) * ∏ i,
        outcomeTaylorPolynomial (R i) (T i) (ψ i * amp) (jb i) (η i)
          (offset i + ψ i * coefficientEvaluation (U ω) (sites i)) (rough i) (X (keep i))) -
        C (μ.expect (fun ω => ∏ i, likelihood (R i) (T i) (jb i) (η i)
          (offset i + ψ i * coefficientEvaluation (U ω) (sites i)) (rough i))) := by
  apply MvPolynomial.funext
  intro z
  rw [coefficientShiftPolynomial_eval]
  simp only [map_sub, map_sum, map_mul, map_prod, eval_C, outcomeTaylorPolynomial_eval, eval_X,
    retainedOutcomePolynomial_eval]
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
  congr 1
  ring

theorem outcomeCoefficientFunctional_retained {J : Type*} [Fintype J] [DecidableEq J]
    (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (u : V × d → ℝ) (τ amp : ℝ) (keep : I → V) (sites : I → d → ℝ)
    (hkeep : ∀ i, configurationSite u (keep i) = sites i)
    (R T jb η rough offset ψ : I → ℝ) (κ : V → ℝ)
    (W : Representative.Array d V J 3) (z : V → ℝ) (ζ : J → Bool) :
    outcomeCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ κ W u z ζ
      (retainedOutcomePolynomial Q R T jb η rough offset ψ sites) =
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) *
        (μ.expect (fun ω => outcomePolynomialFunctional κ W u z ζ
          (∏ i, outcomeTaylorPolynomial (R i) (T i) (ψ i * amp) (jb i) (η i)
            (offset i + ψ i * coefficientEvaluation (U ω) (sites i)) (rough i) (X (keep i)))) -
          μ.expect (fun ω => ∏ i, likelihood (R i) (T i) (jb i) (η i)
            (offset i + ψ i * coefficientEvaluation (U ω) (sites i)) (rough i)) *
              Representative.pointValue (Wiener.torusProjection u) z ζ W) := by
  rw [outcomeCoefficientFunctional, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
  by_cases hχ : graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) = 0
  · simp only [hχ, zero_mul]
  · rw [coefficientShiftPolynomial_retained_outcome Q hQ hcard μ U u τ amp keep sites hkeep
      R T jb η rough offset ψ hχ, map_sub, map_sum]
    simp only [MvPolynomial.C_mul', map_smul, smul_eq_mul, outcomePolynomialFunctional_C]
    rfl

end CausalLowerbound.PartC

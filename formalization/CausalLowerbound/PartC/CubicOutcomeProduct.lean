import CausalLowerbound.PartC.CubicFunctionalReindex
import CausalLowerbound.PartC.CubicOutcomeCell

/-! The full multi-block cubic likelihood polynomial matches after
averaging the independent site fields. Independence is explicit at this
stage; the finite row coefficients are arbitrary and remain frozen. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative RoughOutcome
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

theorem assigned_outcome_polynomial_row_matching
    {Ξ : I → Type*} [∀ i, Fintype (Ξ i)] (μ : ∀ i, FiniteLaw (Ξ i)) (rough : ∀ i, Ξ i → ℝ)
    (R T jb η v smooth : I → ℝ) (shift scale : I → K → ℝ) (owner : I → K)
    (hscale : ∀ i k, k ≠ owner i → scale i k = 0) (degree : K → I → Fin 4)
    (hmean : ∀ i, (μ i).expect (rough i) = 0)
    (hvar : ∀ i, (μ i).expect (fun ω => rough i ω ^ 2) = v i)
    (hthird : ∀ i, (μ i).expect (fun ω => rough i ω ^ 3) = 0)
    (hcorrection : ∀ i, ((shift i (owner i) * scale i (owner i)) * jb i * v i) * η i =
      (shift i (owner i) * scale i (owner i)) ^ 3 * jb i * (μ i).expect (fun ω => rough i ω ^ 4)) :
    (FiniteLaw.independent μ).expect (fun ω =>
      cubicSiteFunctional (fun e => ∏ k, ∏ i,
        if e (k, i) = 0 then (scale i k * rough i (ω i)) ^ (degree k i).val else
          outcomeMoment (scale i k ^ 2 * v i) (degree k i) * (scale i k * rough i (ω i)) ^ (e (k, i)).val)
        (∏ i, rename (fun k => (k, i))
          (outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i (ω i))
            (∑ k, C (shift i k) * X k)))) =
      (FiniteLaw.independent μ).expect (fun ω =>
        (∏ k, ∏ i, (scale i k * rough i (ω i)) ^ (degree k i).val) *
          ∏ i, (likelihood (R i) (T i) (jb i) (η i) (smooth i) (rough i (ω i)) +
            realField (R i) (T i) (smooth i) ((shift i (owner i) * scale i (owner i)) * jb i * v i))) := by
  let L := fun i (ω : Ξ i) =>
    cubicSiteFunctional (fun e => ∏ k,
      if e k = 0 then (scale i k * rough i ω) ^ (degree k i).val else
        outcomeMoment (scale i k ^ 2 * v i) (degree k i) * (scale i k * rough i ω) ^ (e k).val)
      (outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i ω)
        (∑ k, C (shift i k) * X k))
  let P := fun i (ω : Ξ i) => (∏ k, (scale i k * rough i ω) ^ (degree k i).val) *
    (likelihood (R i) (T i) (jb i) (η i) (smooth i) (rough i ω) +
      realField (R i) (T i) (smooth i) ((shift i (owner i) * scale i (owner i)) * jb i * v i))
  calc
    _ = (FiniteLaw.independent μ).expect (fun ω => ∏ i, L i (ω i)) := by
      apply FiniteLaw.expect_congr
      intro ω
      exact cubicSiteFunctional_observation_product
        (fun k i e => if e = 0 then (scale i k * rough i (ω i)) ^ (degree k i).val else
          outcomeMoment (scale i k ^ 2 * v i) (degree k i) * (scale i k * rough i (ω i)) ^ e.val) _
    _ = (FiniteLaw.independent μ).expect (fun ω => ∏ i, P i (ω i)) := by
      rw [FiniteLaw.expect_independent_prod μ L, FiniteLaw.expect_independent_prod μ P]
      apply Finset.prod_congr rfl
      intro i _
      exact assigned_outcome_cell_matching (μ i) (rough i) (R i) (T i) (jb i) (η i) (v i) (smooth i)
        (shift i) (scale i) (owner i) (hscale i) (fun k => degree k i)
        (hmean i) (hvar i) (hthird i) (hcorrection i)
    _ = _ := by
      apply FiniteLaw.expect_congr
      intro ω
      dsimp only [P]
      rw [Finset.prod_mul_distrib, Finset.prod_comm]

end CausalLowerbound.PartC

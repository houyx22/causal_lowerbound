import CausalLowerbound.PartC.CubicOutcomeRows
import CausalLowerbound.PartC.RemovedPropensityMatching

/-! Restore the original shared rough-sign law in the complete cubic
row matching. The coefficients may depend on all signs outside the
retained local sets; only those local sets are resampled. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB MvPolynomial Representative RoughOutcome
variable {I K J : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  [Fintype J] [DecidableEq J]

theorem shared_outcome_polynomial_coefficient_matching
    {Rows : K → Type*} [∀ k, Fintype (Rows k)]
    (localSigns : I → Finset J)
    (hS : ∀ i j, i ≠ j → Disjoint (localSigns i) (localSigns j))
    (rough : I → (J → Bool) → ℝ)
    (hrough : ∀ i ζ ζ', (∀ j ∈ localSigns i, ζ j = ζ' j) → rough i ζ = rough i ζ')
    (coeff : (J → Bool) → ∀ k, Rows k → ℝ) (degree : ∀ k, Rows k → I → Fin 4)
    (hcoeff : ∀ ζ ζ', (∀ j, (∀ i, j ∉ localSigns i) → ζ j = ζ' j) → coeff ζ = coeff ζ')
    (R T jb η v smooth : I → ℝ) (shift scale : I → K → ℝ) (owner : I → K)
    (hscale : ∀ i k, k ≠ owner i → scale i k = 0)
    (hmean : ∀ i, independentSigns.expect (rough i) = 0)
    (hvar : ∀ i, independentSigns.expect (fun ζ => rough i ζ ^ 2) = v i)
    (hthird : ∀ i, independentSigns.expect (fun ζ => rough i ζ ^ 3) = 0)
    (hcorrection : ∀ i, ((shift i (owner i) * scale i (owner i)) * jb i * v i) * η i =
      (shift i (owner i) * scale i (owner i)) ^ 3 * jb i * independentSigns.expect (fun ζ => rough i ζ ^ 4)) :
    independentSigns.expect (fun ζ =>
      cubicSiteFunctional (fun e => ∏ k, ∑ r, coeff ζ k r * ∏ i,
        if e (k, i) = 0 then (scale i k * rough i ζ) ^ (degree k r i).val else
          Representative.outcomeMoment (scale i k ^ 2 * v i) (degree k r i) * (scale i k * rough i ζ) ^ (e (k, i)).val)
        (∏ i, rename (fun k => (k, i))
          (outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i ζ)
            (∑ k, C (shift i k) * X k)))) =
      independentSigns.expect (fun ζ =>
        (∏ k, ∑ r, coeff ζ k r * ∏ i, (scale i k * rough i ζ) ^ (degree k r i).val) *
          ∏ i, (likelihood (R i) (T i) (jb i) (η i) (smooth i) (rough i ζ) +
            realField (R i) (T i) (smooth i) ((shift i (owner i) * scale i (owner i)) * jb i * v i))) := by
  let g := fun (ζ : J → Bool) (values : I → ℝ) =>
    cubicSiteFunctional (fun e => ∏ k, ∑ r, coeff ζ k r * ∏ i,
      if e (k, i) = 0 then (scale i k * values i) ^ (degree k r i).val else
        Representative.outcomeMoment (scale i k ^ 2 * v i) (degree k r i) * (scale i k * values i) ^ (e (k, i)).val)
      (∏ i, rename (fun k => (k, i))
        (outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (η i) (smooth i) (values i)
          (∑ k, C (shift i k) * X k)))
  let h := fun (ζ : J → Bool) (values : I → ℝ) =>
    (∏ k, ∑ r, coeff ζ k r * ∏ i, (scale i k * values i) ^ (degree k r i).val) *
      ∏ i, (likelihood (R i) (T i) (jb i) (η i) (smooth i) (values i) +
        realField (R i) (T i) (smooth i) ((shift i (owner i) * scale i (owner i)) * jb i * v i))
  have hg : ∀ ζ ζ' values, (∀ j, (∀ i, j ∉ localSigns i) → ζ j = ζ' j) →
      g ζ values = g ζ' values := by
    intro ζ ζ' values he
    dsimp only [g]
    rw [hcoeff ζ ζ' he]
  have hh : ∀ ζ ζ' values, (∀ j, (∀ i, j ∉ localSigns i) → ζ j = ζ' j) →
      h ζ values = h ζ' values := by
    intro ζ ζ' values he
    dsimp only [h]
    rw [hcoeff ζ ζ' he]
  have hm (base : J → Bool) :
      (FiniteLaw.independent (fun _ : I => independentSigns (ι := J))).expect
        (fun fresh => g base (fun i => rough i (fresh i))) =
      (FiniteLaw.independent (fun _ : I => independentSigns (ι := J))).expect
        (fun fresh => h base (fun i => rough i (fresh i))) :=
    assigned_outcome_polynomial_coefficient_matching (coeff base) degree
      (fun _ : I => independentSigns (ι := J)) rough R T jb η v smooth shift scale owner hscale
      hmean hvar hthird hcorrection
  exact disjoint_sign_matching localSigns hS rough hrough g h hg hh hm

end CausalLowerbound.PartC

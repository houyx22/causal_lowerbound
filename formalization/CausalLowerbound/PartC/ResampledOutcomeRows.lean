import CausalLowerbound.PartC.CubicOutcomeRows
import CausalLowerbound.PartC.ResampledCoefficientMatching

/-! Exact cubic matching with one shared resampled field for all row
coefficients and ghosts. No locality premise on these coefficients is
needed: the union of the retained local sign sets is averaged explicitly. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB MvPolynomial Representative RoughOutcome
variable {I K J : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  [Fintype J] [DecidableEq J]

theorem resampled_outcome_polynomial_coefficient_matching
    {Rows : K → Type*} [∀ k, Fintype (Rows k)]
    (coeff : (J → Bool) → ∀ k, Rows k → ℝ) (degree : ∀ k, Rows k → I → Fin 4)
    (S : I → Finset J) (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (rough : I → (J → Bool) → ℝ)
    (hrough : ∀ i ζ ζ', (∀ j ∈ S i, ζ j = ζ' j) → rough i ζ = rough i ζ')
    (R T jb corr v smooth : I → ℝ) (shift scale : I → K → ℝ) (owner : I → K)
    (hscale : ∀ i k, k ≠ owner i → scale i k = 0)
    (hmean : ∀ i, independentSigns.expect (rough i) = 0)
    (hvar : ∀ i, independentSigns.expect (fun ζ => rough i ζ ^ 2) = v i)
    (hthird : ∀ i, independentSigns.expect (fun ζ => rough i ζ ^ 3) = 0)
    (hcorrection : ∀ i, ((shift i (owner i) * scale i (owner i)) * jb i * v i) * corr i =
      (shift i (owner i) * scale i (owner i)) ^ 3 * jb i * independentSigns.expect (fun ζ => rough i ζ ^ 4)) :
    independentSigns.expect (fun ζ => Walsh.resampleAverage (Finset.univ.biUnion S) (fun η =>
      cubicSiteFunctional (fun e => ∏ k, ∑ r, coeff η k r * ∏ i,
        if e (k, i) = 0 then (scale i k * rough i ζ) ^ (degree k r i).val else
          Representative.outcomeMoment (scale i k ^ 2 * v i) (degree k r i) *
            (scale i k * rough i ζ) ^ (e (k, i)).val)
        (∏ i, rename (fun k => (k, i))
          (outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (corr i) (smooth i) (rough i ζ)
            (∑ k, C (shift i k) * X k)))) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage (Finset.univ.biUnion S) (fun η =>
      (∏ k, ∑ r, coeff η k r * ∏ i, (scale i k * rough i ζ) ^ (degree k r i).val) *
        ∏ i, (likelihood (R i) (T i) (jb i) (corr i) (smooth i) (rough i ζ) +
          realField (R i) (T i) (smooth i) ((shift i (owner i) * scale i (owner i)) * jb i * v i))) ζ) := by
  apply resampled_disjoint_sign_matching S hS rough hrough
    (fun η values => cubicSiteFunctional (fun e => ∏ k, ∑ r, coeff η k r * ∏ i,
      if e (k, i) = 0 then (scale i k * values i) ^ (degree k r i).val else
        Representative.outcomeMoment (scale i k ^ 2 * v i) (degree k r i) *
          (scale i k * values i) ^ (e (k, i)).val)
      (∏ i, rename (fun k => (k, i))
        (outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (corr i) (smooth i) (values i)
          (∑ k, C (shift i k) * X k))))
    (fun η values => (∏ k, ∑ r, coeff η k r * ∏ i, (scale i k * values i) ^ (degree k r i).val) *
      ∏ i, (likelihood (R i) (T i) (jb i) (corr i) (smooth i) (values i) +
        realField (R i) (T i) (smooth i) ((shift i (owner i) * scale i (owner i)) * jb i * v i)))
  intro η
  exact assigned_outcome_polynomial_coefficient_matching (coeff η) degree
    (fun _ : I => independentSigns (ι := J)) rough R T jb corr v smooth shift scale owner hscale
    hmean hvar hthird hcorrection

end CausalLowerbound.PartC

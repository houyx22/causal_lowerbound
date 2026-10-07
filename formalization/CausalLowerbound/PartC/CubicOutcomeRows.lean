import CausalLowerbound.PartC.CubicOutcomeProduct

/-! Sum the complete cubic polynomial matching over all carrier row
choices. Frozen Fourier/Walsh/ghost coefficients may have arbitrary
signs; neither their independence nor positivity is assumed. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative RoughOutcome
variable {I K V : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V]

theorem cubicSiteFunctional_row_expansion {Rows : K → Type*} [∀ k, Fintype (Rows k)]
    (coeff : ∀ k, Rows k → ℝ) (w : ∀ k, Rows k → Degree V 3 → ℝ)
    (p : MvPolynomial V ℝ) :
    cubicSiteFunctional (fun e => ∏ k, ∑ r, coeff k r * w k r e) p =
      ∑ r : ∀ k, Rows k, (∏ k, coeff k (r k)) *
        cubicSiteFunctional (fun e => ∏ k, w k (r k) e) p := by
  have hw : (fun e => ∏ k, ∑ r, coeff k r * w k r e) =
      fun e => ∑ r : ∀ k, Rows k, (∏ k, coeff k (r k)) * ∏ k, w k (r k) e := by
    funext e
    simp only [Fintype.prod_sum, Finset.prod_mul_distrib]
  rw [hw, cubicSiteFunctional_weight_sum]
  simp only [cubicSiteFunctional_weight_mul]

theorem assigned_outcome_polynomial_coefficient_matching
    {Rows : K → Type*} [∀ k, Fintype (Rows k)]
    (coeff : ∀ k, Rows k → ℝ) (degree : ∀ k, Rows k → I → Fin 4)
    {Ξ : I → Type*} [∀ i, Fintype (Ξ i)] (μ : ∀ i, FiniteLaw (Ξ i)) (rough : ∀ i, Ξ i → ℝ)
    (R T jb η v smooth : I → ℝ) (shift scale : I → K → ℝ) (owner : I → K)
    (hscale : ∀ i k, k ≠ owner i → scale i k = 0)
    (hmean : ∀ i, (μ i).expect (rough i) = 0)
    (hvar : ∀ i, (μ i).expect (fun ω => rough i ω ^ 2) = v i)
    (hthird : ∀ i, (μ i).expect (fun ω => rough i ω ^ 3) = 0)
    (hcorrection : ∀ i, ((shift i (owner i) * scale i (owner i)) * jb i * v i) * η i =
      (shift i (owner i) * scale i (owner i)) ^ 3 * jb i * (μ i).expect (fun ω => rough i ω ^ 4)) :
    (FiniteLaw.independent μ).expect (fun ω =>
      cubicSiteFunctional (fun e => ∏ k, ∑ r, coeff k r * ∏ i,
        if e (k, i) = 0 then (scale i k * rough i (ω i)) ^ (degree k r i).val else
          outcomeMoment (scale i k ^ 2 * v i) (degree k r i) *
            (scale i k * rough i (ω i)) ^ (e (k, i)).val)
        (∏ i, rename (fun k => (k, i))
          (outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i (ω i))
            (∑ k, C (shift i k) * X k)))) =
      (FiniteLaw.independent μ).expect (fun ω =>
        (∏ k, ∑ r, coeff k r * ∏ i, (scale i k * rough i (ω i)) ^ (degree k r i).val) *
          ∏ i, (likelihood (R i) (T i) (jb i) (η i) (smooth i) (rough i (ω i)) +
            realField (R i) (T i) (smooth i) ((shift i (owner i) * scale i (owner i)) * jb i * v i))) := by
  let law := FiniteLaw.independent μ
  let P := fun ω : ∀ i, Ξ i => ∏ i, rename (fun k => (k, i))
    (outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i (ω i))
      (∑ k, C (shift i k) * X k))
  let w := fun (ω : ∀ i, Ξ i) (k : K) (r : Rows k) (e : Degree (K × I) 3) => ∏ i,
    if e (k, i) = 0 then (scale i k * rough i (ω i)) ^ (degree k r i).val else
      outcomeMoment (scale i k ^ 2 * v i) (degree k r i) * (scale i k * rough i (ω i)) ^ (e (k, i)).val
  let g := fun (k : K) (r : Rows k) (ω : ∀ i, Ξ i) => ∏ i,
    (scale i k * rough i (ω i)) ^ (degree k r i).val
  let C := fun r : ∀ k, Rows k => ∏ k, coeff k (r k)
  let L := fun ω : ∀ i, Ξ i => ∏ i,
    (likelihood (R i) (T i) (jb i) (η i) (smooth i) (rough i (ω i)) +
      realField (R i) (T i) (smooth i) ((shift i (owner i) * scale i (owner i)) * jb i * v i))
  have hsum (F : (∀ k, Rows k) → (∀ i, Ξ i) → ℝ) :
      law.expect (fun ω => ∑ r, F r ω) = ∑ r, law.expect (F r) := by
    simp only [FiniteLaw.expect, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hmatch (r : ∀ k, Rows k) :
      law.expect (fun ω => cubicSiteFunctional (fun e => ∏ k, w ω k (r k) e) (P ω)) =
        law.expect (fun ω => (∏ k, g k (r k) ω) * L ω) :=
    assigned_outcome_polynomial_row_matching μ rough R T jb η v smooth shift scale owner hscale
      (fun k => degree k (r k)) hmean hvar hthird hcorrection
  change law.expect (fun ω => cubicSiteFunctional (fun e => ∏ k, ∑ r, coeff k r * w ω k r e) (P ω)) =
    law.expect (fun ω => (∏ k, ∑ r, coeff k r * g k r ω) * L ω)
  calc
    _ = law.expect (fun ω => ∑ r : ∀ k, Rows k, C r *
        cubicSiteFunctional (fun e => ∏ k, w ω k (r k) e) (P ω)) := by
      apply law.expect_congr
      intro ω
      exact cubicSiteFunctional_row_expansion coeff (w ω) (P ω)
    _ = ∑ r : ∀ k, Rows k, C r * law.expect (fun ω =>
        cubicSiteFunctional (fun e => ∏ k, w ω k (r k) e) (P ω)) := by
      rw [hsum]
      simp only [law.expect_mul]
    _ = ∑ r : ∀ k, Rows k, C r * law.expect (fun ω => (∏ k, g k (r k) ω) * L ω) := by
      simp only [hmatch]
    _ = law.expect (fun ω => ∑ r : ∀ k, Rows k, C r * ((∏ k, g k (r k) ω) * L ω)) := by
      rw [hsum]
      simp only [law.expect_mul]
    _ = _ := by
      apply law.expect_congr
      intro ω
      simp only [Fintype.prod_sum, Finset.prod_mul_distrib, Finset.sum_mul, C]
      apply Finset.sum_congr rfl
      intro r _
      ring

end CausalLowerbound.PartC

import CausalLowerbound.PartC.CubicTaylorEvaluation

/-! Exact design-weighted matching of the full cubic likelihood product
under independent rough fields. The Fourier--Walsh row coefficients stay
fixed; shared-sign dependence is handled by the subsequent removal step. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative RoughOutcome
variable {V d J : Type*} [Fintype V] [DecidableEq V]
  [Fintype d] [Fintype J] [DecidableEq J]

theorem frozen_outcome_polynomial_matching
    {Ξ : V → Type*} [∀ i, Fintype (Ξ i)] (μ : ∀ i, FiniteLaw (Ξ i)) (F : ∀ i, Ξ i → ℝ)
    (R T shift jb η v scale smooth : V → ℝ)
    (hmean : ∀ i, (μ i).expect (F i) = 0)
    (hvar : ∀ i, (μ i).expect (fun ω => F i ω ^ 2) = v i)
    (hthird : ∀ i, (μ i).expect (fun ω => F i ω ^ 3) = 0)
    (hcorrection : ∀ i, ((shift i * scale i) * jb i * v i) * η i =
      (shift i * scale i) ^ 3 * jb i * (μ i).expect (fun ω => F i ω ^ 4))
    (W : Representative.Array d V J 3) (u : V × d → ℝ) (ζ : J → Bool) :
    (FiniteLaw.independent μ).expect (fun ω =>
      outcomePolynomialFunctional (fun i => scale i ^ 2 * v i) W u (fun i => scale i * F i (ω i)) ζ
        (∏ i, outcomeTaylorPolynomial (R i) (T i) (shift i) (jb i) (η i) (smooth i) (F i (ω i)) (X i))) =
      (FiniteLaw.independent μ).expect (fun ω =>
        pointValue (Wiener.torusProjection u) (fun i => scale i * F i (ω i)) ζ W *
          ∏ i, (likelihood (R i) (T i) (jb i) (η i) (smooth i) (F i (ω i)) +
            realField (R i) (T i) (smooth i) ((shift i * scale i) * jb i * v i))) := by
  let law := FiniteLaw.independent μ
  let z (ω : ∀ i, Ξ i) (i : V) := scale i * F i (ω i)
  let a (ω : ∀ i, Ξ i) (i : V) := likelihood (R i) (T i) (jb i) (η i) (smooth i) (F i (ω i))
  let g (ω : ∀ i, Ξ i) (i : V) := a ω i +
    realField (R i) (T i) (smooth i) ((shift i * scale i) * jb i * v i)
  let c (r : Row V J 3) := Walsh.character r.2 ζ * (Wiener.toContinuous (W r) (Wiener.torusProjection u)).re
  have hsum (f : Row V J 3 → (∀ i, Ξ i) → ℝ) :
      law.expect (fun ω => ∑ r, f r ω) = ∑ r, law.expect (f r) := by
    simp only [FiniteLaw.expect, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hrow (e : Degree V 3) :
      law.expect (fun ω => ∏ i, (z ω i ^ (e i).val * a ω i +
        normalizedIncrement (e i) (scale i) (v i) (R i) (T i) (shift i) (jb i) (η i) (smooth i) (F i (ω i)))) =
      law.expect (fun ω => ∏ i, (z ω i ^ (e i).val * g ω i)) := by
    let L := fun i (ω : Ξ i) => (scale i * F i ω) ^ (e i).val *
      likelihood (R i) (T i) (jb i) (η i) (smooth i) (F i ω) +
        normalizedIncrement (e i) (scale i) (v i) (R i) (T i) (shift i) (jb i) (η i) (smooth i) (F i ω)
    let P := fun i (ω : Ξ i) => (scale i * F i ω) ^ (e i).val *
      (likelihood (R i) (T i) (jb i) (η i) (smooth i) (F i ω) +
        realField (R i) (T i) (smooth i) ((shift i * scale i) * jb i * v i))
    change (FiniteLaw.independent μ).expect (fun ω => ∏ i, L i (ω i)) =
      (FiniteLaw.independent μ).expect (fun ω => ∏ i, P i (ω i))
    rw [FiniteLaw.expect_independent_prod μ L, FiniteLaw.expect_independent_prod μ P]
    apply Finset.prod_congr rfl
    intro i _
    exact normalized_cell_bridge (μ i) (F i) (R i) (T i) (shift i) (jb i) (η i) (smooth i) (v i) (scale i)
      (hmean i) (hvar i) (hthird i) (hcorrection i) (e i)
  simp_rw [outcomePolynomialFunctional_taylor]
  change law.expect (fun ω => ∑ r : Row V J 3, c r *
    ∏ i, (z ω i ^ (r.1 i).val * a ω i +
      normalizedIncrement (r.1 i) (scale i) (v i) (R i) (T i) (shift i) (jb i) (η i) (smooth i) (F i (ω i)))) =
    law.expect (fun ω => pointValue (Wiener.torusProjection u) (z ω) ζ W * ∏ i, g ω i)
  rw [hsum]
  simp_rw [law.expect_mul, hrow]
  calc
    _ = law.expect (fun ω => ∑ r : Row V J 3,
        c r * ((∏ i, z ω i ^ (r.1 i).val) * ∏ i, g ω i)) := by
      rw [hsum]
      apply Finset.sum_congr rfl
      intro r _
      rw [← law.expect_mul]
      apply law.expect_congr
      intro ω
      rw [Finset.prod_mul_distrib]
    _ = _ := by
      apply law.expect_congr
      intro ω
      simp only [pointValue, rowWeight, Representative.monomial, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      dsimp [c]
      ring

end CausalLowerbound.PartC

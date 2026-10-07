import CausalLowerbound.PartC.OutcomePolynomialTarget

/-! Exact action of the cubic site functional on products of cubic
site polynomials. All four input design degrees are retained. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative
variable {V d J : Type*} [Fintype V] [DecidableEq V]
  [Fintype d] [Fintype J] [DecidableEq J]

theorem cubicSiteFunctional_prod_pow (w : Degree V 3 → ℝ) (a : Degree V 3) :
    cubicSiteFunctional w (∏ i, X i ^ (a i).val) = w a := by
  let e : V →₀ ℕ := ∑ i, Finsupp.single i (a i).val
  have he (i : V) : e i = (a i).val := by simp [e, Finsupp.single_apply]
  have hp : (∏ i, X i ^ (a i).val : MvPolynomial V ℝ) = MvPolynomial.monomial e 1 := by
    apply MvPolynomial.funext
    intro z
    simp only [map_prod, map_pow, eval_X, eval_monomial, one_mul]
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero (z i))]
    simp only [he]
  have hdeg : ∀ i, e i ≤ 3 := fun i => (he i).le.trans (Nat.le_of_lt_succ (a i).isLt)
  rw [hp, cubicSiteFunctional_monomial, dif_pos hdeg, one_mul]
  congr 1
  funext i
  exact Fin.ext (he i)

theorem cubicSiteFunctional_product (w : Degree V 3 → ℝ) (c : V → Fin 4 → ℝ) :
    cubicSiteFunctional w (∏ i, ∑ f : Fin 4, C (c i f) * X i ^ f.val) =
      ∑ e : Degree V 3, (∏ i, c i (e i)) * w e := by
  rw [Fintype.prod_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.prod_mul_distrib, ← map_prod, MvPolynomial.C_mul', map_smul, smul_eq_mul,
    cubicSiteFunctional_prod_pow]

theorem cubicSiteFunctional_product_weight (c w : V → Fin 4 → ℝ) :
    cubicSiteFunctional (fun e => ∏ i, w i (e i)) (∏ i, ∑ f : Fin 4, C (c i f) * X i ^ f.val) =
      ∏ i, ∑ f : Fin 4, c i f * w i f := by
  rw [cubicSiteFunctional_product, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact (Finset.prod_mul_distrib).symm

theorem cubicSiteFunctional_weight_sum {I : Type*} [Fintype I]
    (w : I → Degree V 3 → ℝ) (p : MvPolynomial V ℝ) :
    cubicSiteFunctional (fun e => ∑ i, w i e) p = ∑ i, cubicSiteFunctional (w i) p := by
  change (∑ e ∈ p.support, p.coeff e * (if he : ∀ i, e i ≤ 3 then ∑ i, w i (cubicSiteDegree e he) else 0)) =
    ∑ i, ∑ e ∈ p.support, p.coeff e * (if he : ∀ j, e j ≤ 3 then w i (cubicSiteDegree e he) else 0)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : ∀ i, e i ≤ 3
  · simp only [dif_pos he, Finset.mul_sum]
  · simp only [dif_neg he, mul_zero, Finset.sum_const_zero]

theorem cubicSiteFunctional_weight_mul (c : ℝ) (w : Degree V 3 → ℝ) (p : MvPolynomial V ℝ) :
    cubicSiteFunctional (fun e => c * w e) p = c * cubicSiteFunctional w p := by
  change (∑ e ∈ p.support, p.coeff e * (if he : ∀ i, e i ≤ 3 then c * w (cubicSiteDegree e he) else 0)) =
    c * ∑ e ∈ p.support, p.coeff e * (if he : ∀ i, e i ≤ 3 then w (cubicSiteDegree e he) else 0)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : ∀ i, e i ≤ 3
  · simp only [dif_pos he]
    ring
  · simp only [dif_neg he]
    ring

theorem outcomePolynomialFunctional_cubic (κ : V → ℝ) (v : Representative.Array d V J 3)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (c : V → Fin 4 → ℝ) :
    outcomePolynomialFunctional κ v u z ζ (∏ i, ∑ f : Fin 4, C (c i f) * X i ^ f.val) =
      ∑ r : Row V J 3, Walsh.character r.2 ζ * (Wiener.toContinuous (v r) (Wiener.torusProjection u)).re *
        ∏ i, ∑ f : Fin 4, c i f *
          (if f = 0 then z i ^ (r.1 i).val else Representative.outcomeMoment (κ i) (r.1 i) * z i ^ f.val) := by
  change cubicSiteFunctional (fun e => ∑ r : Row V J 3,
    (Walsh.character r.2 ζ * (Wiener.toContinuous (v r) (Wiener.torusProjection u)).re) *
      ∏ i, outcomeSlotFactor e κ z r.1 i) _ = _
  rw [cubicSiteFunctional_weight_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [cubicSiteFunctional_weight_mul]
  congr 1
  exact cubicSiteFunctional_product_weight c (fun i f =>
    if f = 0 then z i ^ (r.1 i).val else Representative.outcomeMoment (κ i) (r.1 i) * z i ^ f.val)

end CausalLowerbound.PartC

import CausalLowerbound.PartC.BlockCubicFunctional

/-! Reindex cubic functionals between block/observation and
observation/block coordinates. No support or degree is lost by this
change of variables. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative
variable {V W K : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W] [Fintype K] [DecidableEq K]

theorem cubicSiteFunctional_rename_equiv (e : V ≃ W) (w : Degree W 3 → ℝ)
    (p : MvPolynomial V ℝ) :
    cubicSiteFunctional w (rename e p) =
      cubicSiteFunctional (fun f => w (fun i => f (e.symm i))) p := by
  let L := (cubicSiteFunctional w).comp (rename e).toLinearMap
  let R := cubicSiteFunctional (fun f => w (fun i => f (e.symm i)))
  change L p = R p
  rw [polynomial_linear_expansion L p, polynomial_linear_expansion R p]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  simp only [L, R, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    rename_monomial, cubicSiteFunctional_monomial, one_mul]
  by_cases hm : ∀ i, m i ≤ 3
  · have he : ∀ i, m.mapDomain e i ≤ 3 := by
      intro i
      rw [Finsupp.mapDomain_equiv_apply]
      exact hm (e.symm i)
    rw [dif_pos he, dif_pos hm]
    congr 1
    funext i
    apply Fin.ext
    exact Finsupp.mapDomain_equiv_apply m i
  · have he : ¬ ∀ i, m.mapDomain e i ≤ 3 := by
      intro h
      apply hm
      intro i
      simpa only [Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply] using h (e i)
    rw [dif_neg he, dif_neg hm]

theorem cubicSiteFunctional_observation_product (w : K → V → Fin 4 → ℝ)
    (p : V → MvPolynomial K ℝ) :
    cubicSiteFunctional (fun e => ∏ k, ∏ i, w k i (e (k, i)))
      (∏ i, rename (fun k => (k, i)) (p i)) =
      ∏ i, cubicSiteFunctional (fun e => ∏ k, w k i (e k)) (p i) := by
  have hp : (∏ i, rename (fun k => (k, i)) (p i)) =
      rename (Equiv.prodComm V K) (∏ i, rename (fun k => (i, k)) (p i)) := by
    simp only [map_prod, rename_rename, Function.comp_def, Equiv.prodComm_apply, Prod.swap]
  rw [hp, cubicSiteFunctional_rename_equiv]
  have hw : (fun e : Degree (V × K) 3 => ∏ k, ∏ i, w k i (e (i, k))) =
      fun e => ∏ i, ∏ k, w k i (e (i, k)) := by
    funext e
    exact Finset.prod_comm
  change cubicSiteFunctional (fun e => ∏ k, ∏ i, w k i (e (i, k))) _ = _
  rw [hw]
  exact cubicSiteFunctional_block_product (fun i e => ∏ k, w k i (e k)) p

end CausalLowerbound.PartC

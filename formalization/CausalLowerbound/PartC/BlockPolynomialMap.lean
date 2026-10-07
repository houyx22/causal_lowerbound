import CausalLowerbound.PartC.BlockCoefficientShift

/-! Apply an algebraic substitution separately in every block. Tensor
polynomial functionals commute with this substitution even when their
one-block factors are merely linear and are not multiplicative. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial
variable {K A V : Type*} [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]

def blockPolynomialMap (T : K → MvPolynomial A ℝ →ₐ[ℝ] MvPolynomial V ℝ) :
    MvPolynomial (K × A) ℝ →ₐ[ℝ] MvPolynomial (K × V) ℝ :=
  aeval (fun ka => rename (fun v => (ka.1, v)) (T ka.1 (X ka.2)))

@[simp] theorem blockPolynomialMap_X (T : K → MvPolynomial A ℝ →ₐ[ℝ] MvPolynomial V ℝ)
    (k : K) (a : A) :
    blockPolynomialMap T (X (k, a)) = rename (fun v => (k, v)) (T k (X a)) := by
  simp only [blockPolynomialMap, aeval_X]

theorem blockPolynomialMap_rename (T : K → MvPolynomial A ℝ →ₐ[ℝ] MvPolynomial V ℝ)
    (k : K) (p : MvPolynomial A ℝ) :
    blockPolynomialMap T (rename (fun a => (k, a)) p) =
      rename (fun v => (k, v)) (T k p) := by
  have he : (blockPolynomialMap T).comp (rename (fun a => (k, a))) =
      (rename (fun v => (k, v))).comp (T k) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, rename_X, blockPolynomialMap_X]
  exact AlgHom.congr_fun he p

theorem blockPolynomialMap_separated_product
    (T : K → MvPolynomial A ℝ →ₐ[ℝ] MvPolynomial V ℝ) (p : K → MvPolynomial A ℝ) :
    blockPolynomialMap T (∏ k, rename (fun a => (k, a)) (p k)) =
      ∏ k, rename (fun v => (k, v)) (T k (p k)) := by
  simp only [map_prod, blockPolynomialMap_rename]

theorem blockPolynomialFunctional_map
    (T : K → MvPolynomial A ℝ →ₐ[ℝ] MvPolynomial V ℝ)
    (L : K → MvPolynomial V ℝ →ₗ[ℝ] ℝ) (p : MvPolynomial (K × A) ℝ) :
    blockPolynomialFunctional L (blockPolynomialMap T p) =
      blockPolynomialFunctional (fun k => (L k).comp (T k).toLinearMap) p := by
  let F := (blockPolynomialFunctional L).comp (blockPolynomialMap T).toLinearMap
  let H := blockPolynomialFunctional (fun k => (L k).comp (T k).toLinearMap)
  have hm (m : (K × A) →₀ ℕ) : F (monomial m 1) = H (monomial m 1) := by
    dsimp only [F, H, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    conv_lhs => rw [monomial_separated_block_product, blockPolynomialMap_separated_product,
      blockPolynomialFunctional_separated_product]
    rw [blockPolynomialFunctional_monomial, one_mul]
    rfl
  change F p = H p
  rw [polynomial_linear_expansion F p, polynomial_linear_expansion H p]
  apply Finset.sum_congr rfl
  intro m _
  exact congrArg (fun z : ℝ => p.coeff m * z) (hm m)

end CausalLowerbound.PartC

import CausalLowerbound.PartC.BlockCoefficientShift
import CausalLowerbound.PartC.CubicSitePolynomial

/-! Tensor products of cubic site functionals retain all block/slot
degrees. The coefficient average commutes with this tensor operation
without requiring a functional to be multiplicative. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative
variable {K V A Ω : Type*} [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A] [Fintype Ω]

theorem block_cubic_pattern_product (w : K → Degree V 3 → ℝ) (m : (K × V) →₀ ℕ) :
    (∏ k, cubicSiteFunctional (w k) (blockMonomial m k)) =
      if hm : ∀ v, m v ≤ 3 then ∏ k, w k (fun v => cubicSiteDegree m hm (k, v)) else 0 := by
  by_cases hm : ∀ v, m v ≤ 3
  · rw [dif_pos hm]
    apply Finset.prod_congr rfl
    intro k _
    have hk : ∀ v, blockExponent m k v ≤ 3 := fun v => by
      rw [blockExponent_apply]
      exact hm (k, v)
    rw [blockMonomial, cubicSiteFunctional_monomial, dif_pos hk, one_mul]
    congr 1
  · rw [dif_neg hm]
    obtain ⟨⟨k, v⟩, hv⟩ := not_forall.mp hm
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    have hk : ¬ ∀ v, blockExponent m k v ≤ 3 := by
      intro he
      exact hv (by simpa only [blockExponent_apply] using he v)
    rw [blockMonomial, cubicSiteFunctional_monomial, dif_neg hk, mul_zero]

theorem blockPolynomialFunctional_cubic_patterns (w : K → Degree V 3 → ℝ)
    (p : MvPolynomial (K × V) ℝ) :
    blockPolynomialFunctional (fun k => cubicSiteFunctional (w k)) p =
      cubicSiteFunctional (fun e => ∏ k, w k (fun v => e (k, v))) p := by
  rw [blockPolynomialFunctional_expansion]
  change (∑ m ∈ p.support, p.coeff m * ∏ k, cubicSiteFunctional (w k) (blockMonomial m k)) =
    ∑ m ∈ p.support, p.coeff m *
      (if hm : ∀ v, m v ≤ 3 then ∏ k, w k (fun v => cubicSiteDegree m hm (k, v)) else 0)
  simp_rw [block_cubic_pattern_product]

theorem cubicSiteFunctional_block_product (w : K → Degree V 3 → ℝ)
    (p : K → MvPolynomial V ℝ) :
    cubicSiteFunctional (fun e => ∏ k, w k (fun v => e (k, v)))
      (∏ k, rename (fun v => (k, v)) (p k)) = ∏ k, cubicSiteFunctional (w k) (p k) := by
  rw [← blockPolynomialFunctional_cubic_patterns, blockPolynomialFunctional_separated_product]

theorem blockPolynomialFunctional_cubic_shift_average
    (μ : K → FiniteLaw Ω) (U : K → Ω → A → ℝ)
    (c : K → A → V → ℝ) (amp : K → ℝ) (w : K → Degree V 3 → ℝ)
    (p : MvPolynomial (K × A) ℝ) :
    blockPolynomialFunctional (fun k => (cubicSiteFunctional (w k)).comp
      (coefficientShiftAverage (μ k) (U k) (c k) (amp k))) p =
      cubicSiteFunctional (fun e => ∏ k, w k (fun v => e (k, v)))
        (blockShiftAverage μ U c amp p) := by
  let L := blockPolynomialFunctional (fun k => (cubicSiteFunctional (w k)).comp
    (coefficientShiftAverage (μ k) (U k) (c k) (amp k)))
  let R := (cubicSiteFunctional (fun e => ∏ k, w k (fun v => e (k, v)))).comp
    (blockShiftAverage μ U c amp)
  have hm (m : (K × A) →₀ ℕ) : L (monomial m 1) = R (monomial m 1) := by
    dsimp only [L, R, LinearMap.comp_apply]
    rw [blockPolynomialFunctional_monomial, one_mul]
    conv_rhs => rw [monomial_separated_block_product, blockShiftAverage_separated_product,
      cubicSiteFunctional_block_product]
    rfl
  change L p = R p
  rw [polynomial_linear_expansion L p, polynomial_linear_expansion R p]
  apply Finset.sum_congr rfl
  intro m _
  exact congrArg (fun a : ℝ => p.coeff m * a) (hm m)

end CausalLowerbound.PartC

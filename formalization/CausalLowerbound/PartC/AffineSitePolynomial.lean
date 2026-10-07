import CausalLowerbound.PartC.PropensityPolynomialTarget

/-! Exact action of the truncated site functional on products of affine
site factors. These are the smooth-field factors in the rough propensity
likelihood. The formula retains every design degree, including zero. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative
variable {V d J : Type*} [Fintype V] [DecidableEq V]
  [Fintype d] [Fintype J] [DecidableEq J]

theorem sitePatternFunctional_finset_X (w : Finset V → ℝ) (S : Finset V) :
    sitePatternFunctional w (∏ i ∈ S, X i) = w S := by
  have hi : (Finset.univ.image (fun i : S => i.val)) = S := by ext i; simp
  have hh := sitePatternFunctional_prod_X w (fun i : S => i.val)
  simpa only [Finset.prod_coe_sort, if_pos Subtype.val_injective, hi] using hh

theorem sitePatternFunctional_affine_product (w : Finset V → ℝ) (a b : V → ℝ) :
    sitePatternFunctional w (∏ i, (C (b i) * X i + C (a i))) =
      ∑ S : Finset V, ((∏ i ∈ S, b i) * ∏ i ∈ Sᶜ, a i) * w S := by
  rw [Fintype.prod_add, map_sum]
  apply Finset.sum_congr rfl
  intro S _
  have hp : (∏ i ∈ S, C (b i) * X i) * (∏ i ∈ Sᶜ, C (a i)) =
      C ((∏ i ∈ S, b i) * ∏ i ∈ Sᶜ, a i) * (∏ i ∈ S, X i : MvPolynomial V ℝ) := by
    rw [Finset.prod_mul_distrib, ← map_prod, ← map_prod, map_mul]
    ring
  rw [hp, MvPolynomial.C_mul', map_smul, smul_eq_mul, sitePatternFunctional_finset_X]

def productPatternWeight (v₀ v₁ : V → ℝ) (S : Finset V) : ℝ :=
  (∏ i ∈ S, v₁ i) * ∏ i ∈ Sᶜ, v₀ i

theorem sitePatternFunctional_product_weight (a b v₀ v₁ : V → ℝ) :
    sitePatternFunctional (productPatternWeight v₀ v₁) (∏ i, (C (b i) * X i + C (a i))) =
      ∏ i, (b i * v₁ i + a i * v₀ i) := by
  rw [sitePatternFunctional_affine_product, Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  simp only [productPatternWeight, Finset.prod_mul_distrib]
  ring

theorem sitePatternFunctional_weight_sum {I : Type*} [Fintype I]
    (w : I → Finset V → ℝ) (p : MvPolynomial V ℝ) :
    sitePatternFunctional (fun S => ∑ i, w i S) p = ∑ i, sitePatternFunctional (w i) p := by
  change (∑ e ∈ p.support, p.coeff e * (if ∀ i, e i ≤ 1 then ∑ i, w i e.support else 0)) =
    ∑ i, ∑ e ∈ p.support, p.coeff e * (if ∀ j, e j ≤ 1 then w i e.support else 0)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : ∀ i, e i ≤ 1
  · simp only [if_pos he, Finset.mul_sum]
  · simp only [if_neg he, mul_zero, Finset.sum_const_zero]

theorem sitePatternFunctional_weight_mul (c : ℝ) (w : Finset V → ℝ) (p : MvPolynomial V ℝ) :
    sitePatternFunctional (fun S => c * w S) p = c * sitePatternFunctional w p := by
  change (∑ e ∈ p.support, p.coeff e * (if ∀ i, e i ≤ 1 then c * w e.support else 0)) =
    c * ∑ e ∈ p.support, p.coeff e * (if ∀ i, e i ≤ 1 then w e.support else 0)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : ∀ i, e i ≤ 1
  · simp only [if_pos he]
    ring
  · simp only [if_neg he]
    ring

theorem propensitySlotFactor_prod (S : Finset V) (κ z : V → ℝ) (e : Degree V 1) :
    (∏ i, propensitySlotFactor S κ z e i) =
      productPatternWeight (fun i => z i ^ (e i).val) (fun i => if e i = 0 then z i else κ i) S := by
  unfold propensitySlotFactor productPatternWeight
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.compl_eq_univ_sdiff, Finset.sdiff_eq_filter]

theorem propensityPolynomialFunctional_affine (κ : V → ℝ) (v : Representative.Array d V J 1)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (a b : V → ℝ) :
    propensityPolynomialFunctional κ v u z ζ (∏ i, (C (b i) * X i + C (a i))) =
      ∑ r : Row V J 1, Walsh.character r.2 ζ * (Wiener.toContinuous (v r) (Wiener.torusProjection u)).re *
        ∏ i, (b i * (if r.1 i = 0 then z i else κ i) + a i * z i ^ (r.1 i).val) := by
  change sitePatternFunctional (fun S => ∑ r : Row V J 1,
    (Walsh.character r.2 ζ * (Wiener.toContinuous (v r) (Wiener.torusProjection u)).re) *
      ∏ i, propensitySlotFactor S κ z r.1 i) _ = _
  rw [sitePatternFunctional_weight_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [sitePatternFunctional_weight_mul]
  simp only [propensitySlotFactor_prod, sitePatternFunctional_product_weight]

end CausalLowerbound.PartC

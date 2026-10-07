import CausalLowerbound.FiniteProductMixture

/-! Regrouping a finite independent law by fibers of an arbitrary map.
This is the finite probability step behind component factorization. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.FiniteLaw
variable {K C Ω : Type*} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C] [Fintype Ω]

def fiberGrouping (c : K → C) : (K → Ω) ≃ ((a : C) → ({k // c k = a} → Ω)) where
  toFun x a k := x k.val
  invFun y k := y (c k) ⟨k, rfl⟩
  left_inv _ := rfl
  right_inv y := by
    funext a ⟨k, hk⟩
    subst a
    rfl

theorem expect_independent_grouped (μ : K → FiniteLaw Ω) (c : K → C) (f : (K → Ω) → ℝ) :
    (independent μ).expect f =
      (independent (fun a => independent (fun k : {k // c k = a} => μ k.val))).expect
        (fun y => f ((fiberGrouping c).symm y)) := by
  simp only [expect, independent]
  rw [← (fiberGrouping c).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [(fiberGrouping c).symm_apply_apply]
  have hw := Fintype.prod_fiberwise c (fun k => (μ k).weight (x k))
  exact congrArg (fun w => w * f x) hw.symm

theorem expect_independent_component_prod (μ : K → FiniteLaw Ω) (c : K → C)
    (f : (a : C) → ({k // c k = a} → Ω) → ℝ) :
    (independent μ).expect (fun x => ∏ a, f a (fun k => x k.val)) =
      ∏ a, (independent (fun k : {k // c k = a} => μ k.val)).expect (f a) := by
  rw [expect_independent_grouped μ c]
  have he (y : (a : C) → ({k // c k = a} → Ω)) :
      (∏ a, f a (fun k => (fiberGrouping c).symm y k.val)) = ∏ a, f a (y a) := by
    have h := (fiberGrouping c).apply_symm_apply y
    change (∏ a, f a ((fiberGrouping c) ((fiberGrouping c).symm y) a)) = _
    rw [h]
  simp_rw [he]
  exact expect_independent_prod _ _

end CausalLowerbound.FiniteLaw

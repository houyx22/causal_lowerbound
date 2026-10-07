import CausalLowerbound.FinitePushforward
import Mathlib.Logic.Equiv.Set

/-! Reindexing and projecting genuine finite product probability laws. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace CausalLowerbound.FiniteLaw
variable {K J Ω : Type*} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype Ω]

theorem expect_independent_equiv (e : K ≃ J) (μ : J → FiniteLaw Ω) (f : (J → Ω) → ℝ) :
    (independent μ).expect f =
      (independent (fun k => μ (e k))).expect (fun x => f (fun j => x (e.symm j))) := by
  simp only [expect, independent]
  rw [← (Equiv.arrowCongr e (Equiv.refl Ω)).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  have hw : (∏ j, (μ j).weight ((Equiv.arrowCongr e (Equiv.refl Ω)) x j)) =
      ∏ k, (μ (e k)).weight (x k) := by
    rw [← e.prod_comp]
    simp
  rw [hw]
  rfl

theorem expect_independent_sum (μ : K → FiniteLaw Ω) (ν : J → FiniteLaw Ω)
    (f : (K ⊕ J → Ω) → ℝ) :
    (independent (Sum.elim μ ν)).expect f =
      (independent μ).expect (fun x => (independent ν).expect (fun y => f (Sum.elim x y))) := by
  simp only [expect, independent]
  rw [← (Equiv.sumArrowEquivProdArrow K J Ω).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem expect_independent_subtype (μ : K → FiniteLaw Ω) (p : K → Prop) [DecidablePred p]
    (f : ({k // p k} → Ω) → ℝ) :
    (independent μ).expect (fun x => f (fun k => x k.val)) =
      (independent (fun k : {k // p k} => μ k.val)).expect f := by
  rw [expect_independent_equiv (Equiv.sumCompl p) μ (fun x => f (fun k => x k.val))]
  have he : (fun k => μ ((Equiv.sumCompl p) k)) =
      Sum.elim (fun k : {k // p k} => μ k.val) (fun k : {k // ¬p k} => μ k.val) := by
    funext k
    cases k <;> rfl
  rw [he]
  rw [expect_independent_sum]
  simp only [Equiv.sumCompl_apply_symm_of_pos, Subtype.property, Sum.elim_inl, expect_const]

theorem expect_independent_transpose (μ : K → J → FiniteLaw Ω)
    (f : (K → J → Ω) → ℝ) :
    (independent (fun k => independent (μ k))).expect f =
      (independent (fun j => independent (fun k => μ k j))).expect (fun x => f (fun k j => x j k)) := by
  simp only [expect, independent]
  rw [← (Equiv.piComm (fun (_j : J) (_k : K) => Ω)).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_comm]
  rfl

end CausalLowerbound.FiniteLaw

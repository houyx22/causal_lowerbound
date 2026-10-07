import CausalLowerbound.FiniteGrouping
import Mathlib.Logic.Equiv.Prod

/-! Replacing independent coordinates using equal conditional expectations.
This permits tensorization of moment identities without equating the full
coefficient laws or assuming that the likelihood separates by blocks. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.FiniteLaw
variable {K Ω : Type*} [Fintype K] [DecidableEq K] [Fintype Ω] [Inhabited Ω]

theorem expect_independent_split (μ : K → FiniteLaw Ω) (i : K) (f : (K → Ω) → ℝ) :
    (independent μ).expect f =
      (independent (fun j : {j // j ≠ i} => μ j.val)).expect (fun rest =>
        (μ i).expect (fun z => f ((Equiv.funSplitAt i Ω).symm (z, rest)))) := by
  have hw (z : Ω × ({j // j ≠ i} → Ω)) :
      (∏ k, (μ k).weight ((Equiv.funSplitAt i Ω).symm z k)) =
        (μ i).weight z.1 * ∏ j : {j // j ≠ i}, (μ j.val).weight (z.2 j) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
    left
    apply Finset.prod_congr rfl
    intro j _
    rw [if_neg j.property]
  simp only [expect, independent]
  rw [← (Equiv.funSplitAt i Ω).symm.sum_comp]
  simp only [hw, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem independent_replace_one (μ ν : K → FiniteLaw Ω) (i : K) (f : (K → Ω) → ℝ)
    (hsame : ∀ j, j ≠ i → μ j = ν j)
    (hslice : ∀ x : K → Ω,
      (μ i).expect (fun z => f (Function.update x i z)) =
        (ν i).expect (fun z => f (Function.update x i z))) :
    (independent μ).expect f = (independent ν).expect f := by
  rw [expect_independent_split μ i f, expect_independent_split ν i f]
  have he : (fun j : {j // j ≠ i} => μ j.val) = (fun j : {j // j ≠ i} => ν j.val) :=
    funext (fun j => hsame j.val j.property)
  rw [he]
  apply expect_congr
  intro rest
  have hu (z : Ω) : Function.update ((Equiv.funSplitAt i Ω).symm (default, rest)) i z =
      (Equiv.funSplitAt i Ω).symm (z, rest) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [Function.update_of_ne hj, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  have hh := hslice ((Equiv.funSplitAt i Ω).symm (default, rest))
  simp_rw [hu] at hh
  exact hh

theorem independent_replace_all (μ ν : K → FiniteLaw Ω) (f : (K → Ω) → ℝ)
    (hslice : ∀ i (x : K → Ω),
      (μ i).expect (fun z => f (Function.update x i z)) =
        (ν i).expect (fun z => f (Function.update x i z))) :
    (independent μ).expect f = (independent ν).expect f := by
  have h (s : Finset K) :
      (independent (fun i => if i ∈ s then ν i else μ i)).expect f = (independent μ).expect f := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      apply Eq.trans _ ih
      apply independent_replace_one _ _ i f
      · intro j hj
        simp [Finset.mem_insert, hj]
      · intro x
        simpa only [Finset.mem_insert_self, if_true, hi, if_false] using (hslice i x).symm
  symm
  simpa using h Finset.univ

end CausalLowerbound.FiniteLaw

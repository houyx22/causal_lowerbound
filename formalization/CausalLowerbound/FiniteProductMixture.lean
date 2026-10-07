import CausalLowerbound.FiniteMixture

/-! Products of finite mixtures and coordinatewise independent mixing. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.FiniteLaw

@[ext] theorem ext {Ω : Type*} [Fintype Ω] {μ ν : FiniteLaw Ω}
    (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ
  cases ν
  congr
  exact funext h

theorem independent_mixture {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Λ Ω : ι → Type*} [∀ i, Fintype (Λ i)] [∀ i, Fintype (Ω i)]
    (μ : ∀ i, FiniteLaw (Λ i)) (laws : ∀ i, Λ i → FiniteLaw (Ω i)) :
    independent (fun i => (μ i).mixture (laws i)) =
      (independent μ).mixture (fun a => independent (fun i => laws i (a i))) := by
  apply ext
  intro x
  simp only [independent, mixture, expect, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun i a => (μ i).weight a * (laws i a).weight (x i))

end CausalLowerbound.FiniteLaw

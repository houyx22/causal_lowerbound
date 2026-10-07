import CausalLowerbound.FiniteProductReplacement

/-! Finite pushforwards and tensorization with different coordinate spaces. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.FiniteLaw
variable {Ω Λ Γ K X : Type*} [Fintype Ω] [Fintype Λ] [Fintype Γ] [Fintype K] [DecidableEq K]

def pointMass (a : Ω) : FiniteLaw Ω where
  weight x := if x = a then 1 else 0
  nonneg _ := by split_ifs <;> norm_num
  total := by simp

theorem expect_pointMass (a : Ω) (f : Ω → ℝ) : (pointMass a).expect f = f a := by
  simp [pointMass, expect]

def map (μ : FiniteLaw Ω) (g : Ω → Λ) : FiniteLaw Λ := μ.mixture (fun x => pointMass (g x))

theorem expect_map (μ : FiniteLaw Ω) (g : Ω → Λ) (f : Λ → ℝ) :
    (μ.map g).expect f = μ.expect (fun x => f (g x)) := by
  rw [map, expect_mixture]
  simp_rw [expect_pointMass]

theorem independent_pointMass (a : K → Ω) : independent (fun i => pointMass (a i)) = pointMass a := by
  apply ext
  intro x
  simp only [independent, pointMass]
  by_cases hx : x = a
  · subst x
    simp
  · rw [if_neg hx]
    have hn : ∃ i, x i ≠ a i := by simpa only [not_forall] using mt funext hx
    obtain ⟨i, hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem independent_map (μ : K → FiniteLaw Ω) (g : K → Ω → Λ) :
    independent (fun i => (μ i).map (g i)) =
      (independent μ).map (fun x i => g i (x i)) := by
  simp only [map]
  rw [independent_mixture]
  simp_rw [independent_pointMass]

theorem expect_independent_map (μ : K → FiniteLaw Ω) (g : K → Ω → Λ) (f : (K → Λ) → ℝ) :
    (independent (fun i => (μ i).map (g i))).expect f =
      (independent μ).expect (fun x => f (fun i => g i (x i))) := by
  rw [independent_map, expect_map]

theorem independent_replace_maps [Inhabited Ω] [Inhabited Λ]
    (μ : K → FiniteLaw Ω) (ν : K → FiniteLaw Λ) (g : K → Ω → X) (h : K → Λ → X)
    (f : (K → X) → ℝ)
    (hslice : ∀ i (x : K → X),
      (μ i).expect (fun z => f (Function.update x i (g i z))) =
        (ν i).expect (fun z => f (Function.update x i (h i z)))) :
    (independent μ).expect (fun x => f (fun i => g i (x i))) =
      (independent ν).expect (fun x => f (fun i => h i (x i))) := by
  let value : K → Ω ⊕ Λ → X := fun i => Sum.elim (g i) (h i)
  have hu (x : K → Ω ⊕ Λ) (i : K) (z : Ω ⊕ Λ) :
      (fun j => value j (Function.update x i z j)) =
        Function.update (fun j => value j (x j)) i (value i z) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hj]
  have he := independent_replace_all (fun i => (μ i).map Sum.inl)
    (fun i => (ν i).map Sum.inr) (fun x => f (fun i => value i (x i))) (by
      intro i x
      simp only [expect_map, hu]
      exact hslice i (fun j => value j (x j)))
  simpa only [expect_independent_map, value, Sum.elim_inl, Sum.elim_inr] using he

theorem expect_independent_prods (μ : K → FiniteLaw Ω) (ν : K → FiniteLaw Λ)
    (f : (K → Ω × Λ) → ℝ) :
    (independent (fun i => (μ i).prod (ν i))).expect f =
      (independent μ).expect (fun x => (independent ν).expect (fun y => f (fun i => (x i, y i)))) := by
  simp only [expect, independent, prod]
  have he := (Equiv.arrowProdEquivProdArrow K (fun _ => Ω) (fun _ => Λ)).symm.sum_comp
    (fun z => (∏ i, (μ i).weight (z i).1 * (ν i).weight (z i).2) * f z)
  rw [← he]
  simp only [Fintype.sum_prod_type, Finset.prod_mul_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  exact mul_assoc _ _ _

end CausalLowerbound.FiniteLaw

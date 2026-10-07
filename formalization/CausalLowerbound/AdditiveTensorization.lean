import CausalLowerbound.FinitePushforward

/-! Tensorization for a function of a sum of independent random fields. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.FiniteLaw
variable {K I Ω Λ : Type*} [Fintype K] [DecidableEq K] [Fintype Ω] [Fintype Λ]
  [Inhabited Ω] [Inhabited Λ]

theorem independent_additive_replacement (μ : K → FiniteLaw Ω) (ν : K → FiniteLaw Λ)
    (g : K → Ω → I → ℝ) (h : K → Λ → I → ℝ) (F : (I → ℝ) → ℝ)
    (hslice : ∀ k (offset : I → ℝ),
      (μ k).expect (fun z => F (fun i => offset i + g k z i)) =
        (ν k).expect (fun z => F (fun i => offset i + h k z i))) :
    (independent μ).expect (fun z => F (fun i => ∑ k, g k (z k) i)) =
      (independent ν).expect (fun z => F (fun i => ∑ k, h k (z k) i)) := by
  apply independent_replace_maps μ ν g h (fun x => F (fun i => ∑ k, x k i))
  intro k x
  have hu (v : I → ℝ) :
      (fun i => ∑ j, Function.update x k v j i) =
        (fun i => (∑ j ∈ Finset.univ.erase k, x j i) + v i) := by
    funext i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  simp_rw [hu]
  exact hslice k (fun i => ∑ j ∈ Finset.univ.erase k, x j i)

end CausalLowerbound.FiniteLaw

import CausalLowerbound.PartC.VectorSeries

/-! Finitely many moment coordinates stacked over a shared countable
dictionary. Only the number of moment coordinates enters the norm bound. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.PartC.VectorSeries

variable {I K E : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem stack_point_bound (a : I → Family K E) (k : K) :
    ‖fun i => a i k‖ ≤ ∑ i, ‖a i k‖ := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
  intro i
  exact Finset.single_le_sum (f := fun j => ‖a j k‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem stack_summable (a : I → Family K E) : Summable (fun k => ‖fun i => a i k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (stack_point_bound a)
    (summable_sum (fun i _ => (hasSum_norm (a i)).summable))

def stackFamily (a : I → Family K E) : Family K (I → E) :=
  ⟨fun k i => a i k, memℓp_gen (by simpa only [ENNReal.toReal_one, Real.rpow_one] using stack_summable a)⟩

@[simp] theorem stackFamily_apply (a : I → Family K E) (k : K) (i : I) :
    stackFamily a k i = a i k := rfl

theorem stackFamily_bound (a : I → Family K E) :
    ‖stackFamily a‖ ≤ (Fintype.card I : ℝ) * ‖a‖ := by
  rw [norm_eq_tsum]
  calc
    _ ≤ ∑' k, ∑ i, ‖a i k‖ := Summable.tsum_le_tsum (stack_point_bound a)
      (stack_summable a) (summable_sum (fun i _ => (hasSum_norm (a i)).summable))
    _ = ∑ i, ‖a i‖ := by
      rw [Summable.tsum_finsetSum (fun i _ => (hasSum_norm (a i)).summable)]
      simp only [← norm_eq_tsum]
    _ ≤ ∑ _i : I, ‖a‖ := Finset.sum_le_sum (fun i _ => norm_le_pi_norm a i)
    _ = _ := by simp

def stack : (I → Family K E) →L[ℝ] Family K (I → E) :=
  LinearMap.mkContinuous
    { toFun := stackFamily
      map_add' := by intro a b; apply lp.ext; rfl
      map_smul' := by intro c a; apply lp.ext; rfl }
    (Fintype.card I : ℝ) stackFamily_bound

@[simp] theorem stack_apply (a : I → Family K E) (k : K) (i : I) : stack a k i = a i k := rfl

theorem stack_bound (a : I → Family K E) :
    ‖stack a‖ ≤ (Fintype.card I : ℝ) * ‖a‖ := stackFamily_bound a

end CausalLowerbound.PartC.VectorSeries

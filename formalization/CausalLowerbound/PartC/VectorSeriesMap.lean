import CausalLowerbound.PartC.VectorSeries

/-! Applying a uniformly bounded linear map to every coefficient. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal

namespace CausalLowerbound.PartC.VectorSeries

variable {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem mapped_summable_norm (T : E →L[ℝ] F) (M : ℝ) (hT : ∀ a, ‖T a‖ ≤ M * ‖a‖)
    (a : Family I E) : Summable (fun i => ‖T (a i)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hT (a i))
    ((hasSum_norm a).summable.mul_left M)

def mappedFamily (T : E →L[ℝ] F) (M : ℝ) (hT : ∀ a, ‖T a‖ ≤ M * ‖a‖)
    (a : Family I E) : Family I F :=
  ⟨fun i => T (a i), memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using mapped_summable_norm T M hT a)⟩

@[simp] theorem mappedFamily_apply (T : E →L[ℝ] F) (M : ℝ) (hT : ∀ a, ‖T a‖ ≤ M * ‖a‖)
    (a : Family I E) (i : I) : mappedFamily T M hT a i = T (a i) := rfl

theorem mappedFamily_bound (T : E →L[ℝ] F) (M : ℝ) (hT : ∀ a, ‖T a‖ ≤ M * ‖a‖)
    (a : Family I E) : ‖mappedFamily T M hT a‖ ≤ M * ‖a‖ := by
  rw [norm_eq_tsum]
  exact (Summable.tsum_le_tsum (fun i => hT (a i)) (mapped_summable_norm T M hT a)
    ((hasSum_norm a).summable.mul_left M)).trans_eq ((hasSum_norm a).mul_left M).tsum_eq

def mapEntries (T : E →L[ℝ] F) (M : ℝ) (hT : ∀ a, ‖T a‖ ≤ M * ‖a‖) : Family I E →L[ℝ] Family I F :=
  LinearMap.mkContinuous
    { toFun := mappedFamily T M hT
      map_add' := by
        intro a b
        apply lp.ext
        funext i
        exact map_add T (a i) (b i)
      map_smul' := by
        intro c a
        apply lp.ext
        funext i
        exact map_smul T c (a i) }
    M (mappedFamily_bound T M hT)

@[simp] theorem mapEntries_apply (T : E →L[ℝ] F) (M : ℝ) (hT : ∀ a, ‖T a‖ ≤ M * ‖a‖)
    (a : Family I E) (i : I) : mapEntries T M hT a i = T (a i) := rfl

theorem mapEntries_bound (T : E →L[ℝ] F) (M : ℝ) (hT : ∀ a, ‖T a‖ ≤ M * ‖a‖)
    (a : Family I E) : ‖mapEntries T M hT a‖ ≤ M * ‖a‖ := mappedFamily_bound T M hT a

end CausalLowerbound.PartC.VectorSeries

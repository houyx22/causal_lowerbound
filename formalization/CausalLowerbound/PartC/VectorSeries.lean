import CausalLowerbound.WienerSeries

/-! Banach-valued absolutely summable coefficients and synthesis by a
uniformly bounded family of continuous linear maps. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace CausalLowerbound.PartC.VectorSeries

abbrev Family (I E : Type*) [NormedAddCommGroup E] := Wiener.Series I E

variable {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasSum_norm (a : Family I E) : HasSum (fun i => ‖a i‖) ‖a‖ := by
  simpa only [ENNReal.toReal_one, Real.rpow_one] using lp.hasSum_norm (p := 1) (by norm_num) a

theorem norm_eq_tsum (a : Family I E) : ‖a‖ = ∑' i, ‖a i‖ := (hasSum_norm a).tsum_eq.symm

def entry (i : I) : Family I E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun a => a i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun a => by simpa only [one_mul] using lp.norm_apply_le_norm (by norm_num) a i)

@[simp] theorem entry_apply (i : I) (a : Family I E) : entry i a = a i := rfl

variable [CompleteSpace F]

theorem summable_synthesis (T : I → E →L[ℝ] F) (M : ℝ) (hT : ∀ i a, ‖T i a‖ ≤ M * ‖a‖)
    (a : Family I E) : Summable (fun i => T i (a i)) := by
  apply Summable.of_norm_bounded (fun i => M * ‖a i‖) ((hasSum_norm a).summable.mul_left M)
  exact fun i => hT i (a i)

theorem norm_synthesis (T : I → E →L[ℝ] F) (M : ℝ) (hT : ∀ i a, ‖T i a‖ ≤ M * ‖a‖)
    (a : Family I E) : ‖∑' i, T i (a i)‖ ≤ M * ‖a‖ :=
  tsum_of_norm_bounded ((hasSum_norm a).mul_left M) (fun i => hT i (a i))

def synthesis (T : I → E →L[ℝ] F) (M : ℝ) (hT : ∀ i a, ‖T i a‖ ≤ M * ‖a‖) : Family I E →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun a => ∑' i, T i (a i)
      map_add' := by
        intro a b
        simp only [lp.coeFn_add, Pi.add_apply, map_add]
        exact (summable_synthesis T M hT a).tsum_add (summable_synthesis T M hT b)
      map_smul' := by
        intro c a
        simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
        exact (summable_synthesis T M hT a).tsum_const_smul c }
    M (norm_synthesis T M hT)

@[simp] theorem synthesis_apply (T : I → E →L[ℝ] F) (M : ℝ) (hT : ∀ i a, ‖T i a‖ ≤ M * ‖a‖)
    (a : Family I E) : synthesis T M hT a = ∑' i, T i (a i) := rfl

theorem synthesis_hasSum (T : I → E →L[ℝ] F) (M : ℝ) (hT : ∀ i a, ‖T i a‖ ≤ M * ‖a‖)
    (a : Family I E) : HasSum (fun i => T i (a i)) (synthesis T M hT a) :=
  (summable_synthesis T M hT a).hasSum

theorem synthesis_single [DecidableEq I] (T : I → E →L[ℝ] F) (M : ℝ)
    (hT : ∀ i a, ‖T i a‖ ≤ M * ‖a‖) (i : I) (a : E) :
    synthesis T M hT (lp.single 1 i a) = T i a := by
  rw [synthesis_apply, tsum_eq_single i]
  · rw [lp.single_apply_self]
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj, map_zero]

end CausalLowerbound.PartC.VectorSeries

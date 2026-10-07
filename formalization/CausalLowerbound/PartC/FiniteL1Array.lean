import CausalLowerbound.WienerSeries
import Mathlib.Analysis.Normed.Group.Constructions

/-! Finite arrays with the sum of the entry norms. Row transformations may
merge indices; their bounds have no factor depending on the number of rows. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace CausalLowerbound.PartC.FiniteL1

abbrev Family (R E : Type*) [NormedAddCommGroup E] := lp (fun _ : R => E) 1

variable {R S E F : Type*} [Fintype R] [Fintype S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def ofFun (f : R → E) : Family R E := ⟨f, memℓp_gen (hasSum_fintype _).summable⟩

@[simp] theorem ofFun_apply (f : R → E) (r : R) : ofFun f r = f r := rfl

theorem norm_eq_sum (a : Family R E) : ‖a‖ = ∑ r, ‖a r‖ := by
  have h := lp.hasSum_norm (p := 1) (by norm_num) a
  simpa only [ENNReal.toReal_one, Real.rpow_one, tsum_fintype] using h.tsum_eq.symm

def entry (r : R) : Family R E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun a => a r
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun a => by simpa only [one_mul] using lp.norm_apply_le_norm (by norm_num) a r)

@[simp] theorem entry_apply (r : R) (a : Family R E) : entry r a = a r := rfl

variable [DecidableEq R] [DecidableEq S]

theorem sum_single (a : Family R E) : (∑ r, lp.single 1 r (a r)) = a := by
  ext r
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  simp

def transform (f : R → S) (T : R → E →L[ℝ] F) (C : ℝ)
    (hT : ∀ r x, ‖T r x‖ ≤ C * ‖x‖) : Family R E →L[ℝ] Family S F :=
  LinearMap.mkContinuous
    { toFun := fun a => ∑ r, lp.single 1 (f r) (T r (a r))
      map_add' := by
        intro a b
        simp only [lp.coeFn_add, Pi.add_apply, map_add, lp.single_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp only [lp.coeFn_smul, Pi.smul_apply, map_smul, lp.single_smul,
          Finset.smul_sum, RingHom.id_apply] }
    C (fun a => by
      calc
        _ ≤ ∑ r, ‖(lp.single 1 (f r) (T r (a r)) : Family S F)‖ := norm_sum_le _ _
        _ = ∑ r, ‖T r (a r)‖ := by
          simp only [lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))]
        _ ≤ ∑ r, C * ‖a r‖ := Finset.sum_le_sum (fun r _ => hT r (a r))
        _ = C * ‖a‖ := by rw [← Finset.mul_sum, norm_eq_sum])

theorem transform_bound (f : R → S) (T : R → E →L[ℝ] F) (C : ℝ)
    (hT : ∀ r x, ‖T r x‖ ≤ C * ‖x‖) (a : Family R E) :
    ‖transform f T C hT a‖ ≤ C * ‖a‖ := by
  calc
    _ ≤ ∑ r, ‖(lp.single 1 (f r) (T r (a r)) : Family S F)‖ := norm_sum_le _ _
    _ = ∑ r, ‖T r (a r)‖ := by
      simp only [lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))]
    _ ≤ ∑ r, C * ‖a r‖ := Finset.sum_le_sum (fun r _ => hT r (a r))
    _ = C * ‖a‖ := by rw [← Finset.mul_sum, norm_eq_sum]

theorem transform_apply (f : R → S) (T : R → E →L[ℝ] F) (C : ℝ)
    (hT : ∀ r x, ‖T r x‖ ≤ C * ‖x‖) (a : Family R E) (s : S) :
    transform f T C hT a s = ∑ r, if s = f r then T r (a r) else 0 := by
  simp only [transform, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]

theorem transform_single (f : R → S) (T : R → E →L[ℝ] F) (C : ℝ)
    (hT : ∀ r x, ‖T r x‖ ≤ C * ‖x‖) (r : R) (x : E) :
    transform f T C hT (lp.single 1 r x) = lp.single 1 (f r) (T r x) := by
  change (∑ s, (lp.single 1 (f s) (T s ((lp.single 1 r x : Family R E) s)) :
    Family S F)) = _
  rw [Finset.sum_eq_single r]
  · rw [lp.single_apply_self]
  · intro s _ hsr
    rw [lp.single_apply_ne _ _ _ hsr, map_zero, lp.single_zero]
  · simp

def diagonal (T : R → E →L[ℝ] E) (C : ℝ) (hT : ∀ r x, ‖T r x‖ ≤ C * ‖x‖) :
    Family R E →L[ℝ] Family R E := transform id T C hT

@[simp] theorem diagonal_apply (T : R → E →L[ℝ] E) (C : ℝ)
    (hT : ∀ r x, ‖T r x‖ ≤ C * ‖x‖) (a : Family R E) (r : R) :
    diagonal T C hT a r = T r (a r) := by
  simp only [diagonal, transform_apply, id_eq]
  simp

def project (p : R → Prop) [DecidablePred p] : Family R E →L[ℝ] Family R E :=
  diagonal (fun r => if p r then ContinuousLinearMap.id ℝ E else 0) 1 (fun r x => by
    dsimp only
    split_ifs <;> simp)

@[simp] theorem project_apply (p : R → Prop) [DecidablePred p] (a : Family R E) (r : R) :
    project p a r = if p r then a r else 0 := by
  rw [project, diagonal_apply]
  split_ifs <;> simp

theorem project_bound (p : R → Prop) [DecidablePred p] (a : Family R E) :
    ‖project p a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using transform_bound id
    (fun r => if p r then ContinuousLinearMap.id ℝ E else 0) 1
    (fun r x => by dsimp only; split_ifs <;> simp) a

theorem project_norm (p : R → Prop) [DecidablePred p] (a : Family R E) :
    ‖project p a‖ = ∑ r, if p r then ‖a r‖ else 0 := by
  rw [norm_eq_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [project_apply]
  split_ifs <;> simp

end CausalLowerbound.PartC.FiniteL1

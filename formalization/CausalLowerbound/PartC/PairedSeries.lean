import CausalLowerbound.PartC.VectorSeries
import Mathlib.Logic.Equiv.Nat
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! Two coefficient sequences share equal norm weights on paired natural
labels. The first coordinate realizes the desired half of each moment;
the second coordinate ensures equal label mass after swapping the pair. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal

namespace CausalLowerbound.PartC.PairedSeries

def labels : ℕ ⊕ ℕ ≃ ℕ := Equiv.natSumNatEquivNat

def flipLabel : Equiv.Perm ℕ := labels.symm.trans ((Equiv.sumComm ℕ ℕ).trans labels)

@[simp] theorem flipLabel_left (n : ℕ) : flipLabel (labels (Sum.inl n)) = labels (Sum.inr n) := by
  change labels ((Equiv.sumComm ℕ ℕ) (labels.symm (labels (Sum.inl n)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem flipLabel_right (n : ℕ) : flipLabel (labels (Sum.inr n)) = labels (Sum.inl n) := by
  change labels ((Equiv.sumComm ℕ ℕ) (labels.symm (labels (Sum.inr n)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def coefficient (a b : VectorSeries.Family ℕ V) (n : ℕ) : V × V :=
  (1 / 2 : ℝ) • Sum.elim (fun m => (a m, b m)) (fun m => (b m, a m)) (labels.symm n)

@[simp] theorem coefficient_left (a b : VectorSeries.Family ℕ V) (n : ℕ) :
    coefficient a b (labels (Sum.inl n)) = (1 / 2 : ℝ) • (a n, b n) := by
  simp only [coefficient, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem coefficient_right (a b : VectorSeries.Family ℕ V) (n : ℕ) :
    coefficient a b (labels (Sum.inr n)) = (1 / 2 : ℝ) • (b n, a n) := by
  simp only [coefficient, Equiv.symm_apply_apply, Sum.elim_inr]

theorem coefficient_flip (a b : VectorSeries.Family ℕ V) (n : ℕ) :
    coefficient a b (flipLabel n) = (coefficient a b n).swap := by
  obtain ⟨s, rfl⟩ := labels.surjective n
  cases s <;> simp only [flipLabel_left, flipLabel_right, coefficient_left, coefficient_right] <;> rfl

theorem coefficient_norm_flip (a b : VectorSeries.Family ℕ V) (n : ℕ) :
    ‖coefficient a b (flipLabel n)‖ = ‖coefficient a b n‖ := by
  rw [coefficient_flip, Prod.norm_def, Prod.norm_def, Prod.fst_swap, Prod.snd_swap, max_comm]

def majorant (a b : VectorSeries.Family ℕ V) (n : ℕ) : ℝ :=
  Sum.elim (fun m => (1 / 2 : ℝ) * (‖a m‖ + ‖b m‖))
    (fun m => (1 / 2 : ℝ) * (‖a m‖ + ‖b m‖)) (labels.symm n)

theorem majorant_hasSum (a b : VectorSeries.Family ℕ V) :
    HasSum (majorant a b) (‖a‖ + ‖b‖) := by
  have hs := ((VectorSeries.hasSum_norm a).add (VectorSeries.hasSum_norm b)).mul_left (1 / 2 : ℝ)
  have hr : HasSum (Sum.elim (fun m => (1 / 2 : ℝ) * (‖a m‖ + ‖b m‖))
      (fun m => (1 / 2 : ℝ) * (‖a m‖ + ‖b m‖)))
      ((1 / 2 : ℝ) * (‖a‖ + ‖b‖) + (1 / 2 : ℝ) * (‖a‖ + ‖b‖)) :=
    HasSum.sum (f := Sum.elim (fun m => (1 / 2 : ℝ) * (‖a m‖ + ‖b m‖))
      (fun m => (1 / 2 : ℝ) * (‖a m‖ + ‖b m‖))) hs hs
  have h : HasSum (majorant a b)
      ((1 / 2 : ℝ) * (‖a‖ + ‖b‖) + (1 / 2 : ℝ) * (‖a‖ + ‖b‖)) :=
    (labels.symm.hasSum_iff (f := Sum.elim (fun m => (1 / 2 : ℝ) * (‖a m‖ + ‖b m‖))
      (fun m => (1 / 2 : ℝ) * (‖a m‖ + ‖b m‖)))).mpr hr
  have he : (1 / 2 : ℝ) * (‖a‖ + ‖b‖) + (1 / 2 : ℝ) * (‖a‖ + ‖b‖) = ‖a‖ + ‖b‖ := by ring
  rwa [he] at h

theorem coefficient_bound (a b : VectorSeries.Family ℕ V) (n : ℕ) :
    ‖coefficient a b n‖ ≤ majorant a b n := by
  unfold coefficient majorant
  cases labels.symm n with
  | inl m =>
    simp only [Sum.elim_inl, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2),
      Prod.norm_def]
    exact mul_le_mul_of_nonneg_left
      (max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))) (by positivity)
  | inr m =>
    simp only [Sum.elim_inr, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2),
      Prod.norm_def]
    exact mul_le_mul_of_nonneg_left
      (max_le (le_add_of_nonneg_left (norm_nonneg _)) (le_add_of_nonneg_right (norm_nonneg _))) (by positivity)

theorem coefficient_summable (a b : VectorSeries.Family ℕ V) :
    Summable (fun n => ‖coefficient a b n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (coefficient_bound a b) (majorant_hasSum a b).summable

def family (a b : VectorSeries.Family ℕ V) : VectorSeries.Family ℕ (V × V) :=
  ⟨coefficient a b, memℓp_gen (by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using coefficient_summable a b)⟩

@[simp] theorem family_apply (a b : VectorSeries.Family ℕ V) (n : ℕ) : family a b n = coefficient a b n := rfl

theorem family_bound (a b : VectorSeries.Family ℕ V) : ‖family a b‖ ≤ ‖a‖ + ‖b‖ := by
  rw [VectorSeries.norm_eq_tsum]
  exact (Summable.tsum_le_tsum (coefficient_bound a b)
    (coefficient_summable a b) (majorant_hasSum a b).summable).trans_eq (majorant_hasSum a b).tsum_eq

def pair : (VectorSeries.Family ℕ V × VectorSeries.Family ℕ V) →L[ℝ] VectorSeries.Family ℕ (V × V) :=
  LinearMap.mkContinuous
    { toFun := fun a => family a.1 a.2
      map_add' := by
        intro a b
        apply lp.ext
        funext n
        change coefficient (a.1 + b.1) (a.2 + b.2) n = coefficient a.1 a.2 n + coefficient b.1 b.2 n
        unfold coefficient
        cases labels.symm n <;> simp [smul_add]
      map_smul' := by
        intro c a
        apply lp.ext
        funext n
        change coefficient (c • a.1) (c • a.2) n = c • coefficient a.1 a.2 n
        unfold coefficient
        cases labels.symm n with
        | inl m => exact smul_comm (1 / 2 : ℝ) c (a.1 m, a.2 m)
        | inr m => exact smul_comm (1 / 2 : ℝ) c (a.2 m, a.1 m) }
    2 (fun a => by
      apply (family_bound a.1 a.2).trans
      have h₁ : ‖a.1‖ ≤ ‖a‖ := norm_fst_le a
      have h₂ : ‖a.2‖ ≤ ‖a‖ := norm_snd_le a
      linarith)

@[simp] theorem pair_apply (a b : VectorSeries.Family ℕ V) : pair (a, b) = family a b := rfl

end CausalLowerbound.PartC.PairedSeries

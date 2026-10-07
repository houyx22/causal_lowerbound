import CausalLowerbound.PartC.PairedSeries
import CausalLowerbound.PartC.CarrierInvolution

/-! Paired linear coefficient maps instantiate the countable carrier
interface. The paired atom family retains its original and reflected
density tensors separately. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal

namespace CausalLowerbound.PartC

open PartB

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def pairedCoefficientOperator (A B : E →L[ℝ] VectorSeries.Family ℕ V) :
    E →L[ℝ] VectorSeries.Family ℕ (V × V) := PairedSeries.pair.comp (A.prod B)

@[simp] theorem pairedCoefficientOperator_apply (A B : E →L[ℝ] VectorSeries.Family ℕ V) (D : E) (n : ℕ) :
    pairedCoefficientOperator A B D n = PairedSeries.coefficient (A D) (B D) n := rfl

theorem pairedCoefficientOperator_bound (A B : E →L[ℝ] VectorSeries.Family ℕ V)
    (L₁ L₂ : ℝ) (hA : ∀ D, ‖A D‖ ≤ L₁ * ‖D‖) (hB : ∀ D, ‖B D‖ ≤ L₂ * ‖D‖) (D : E) :
    ‖pairedCoefficientOperator A B D‖ ≤ (L₁ + L₂) * ‖D‖ :=
  (PairedSeries.family_bound (A D) (B D)).trans ((add_le_add (hA D) (hB D)).trans_eq (add_mul _ _ _).symm)

def pairedCarrierCoefficients (A B : E →L[ℝ] VectorSeries.Family ℕ V)
    (L₁ L₂ : ℝ) (hA : ∀ D, ‖A D‖ ≤ L₁ * ‖D‖) (hB : ∀ D, ‖B D‖ ≤ L₂ * ‖D‖) :
    CarrierCoefficients E (V × V) (L₁ + L₂) where
  coeff D n := pairedCoefficientOperator A B D n
  summable_norm D := (VectorSeries.hasSum_norm (pairedCoefficientOperator A B D)).summable
  zero n := by simp only [map_zero, lp.coeFn_zero, Pi.zero_apply]
  difference_bound D D' := by
    have h := pairedCoefficientOperator_bound A B L₁ L₂ hA hB (D - D')
    rw [map_sub, VectorSeries.norm_eq_tsum] at h
    exact h

theorem pairedCarrierCoefficients_equal_weights (A B : E →L[ℝ] VectorSeries.Family ℕ V)
    (L₁ L₂ : ℝ) (hA : ∀ D, ‖A D‖ ≤ L₁ * ‖D‖) (hB : ∀ D, ‖B D‖ ≤ L₂ * ‖D‖) (D : E) (n : ℕ) :
    ‖(pairedCarrierCoefficients A B L₁ L₂ hA hB).coeff D (PairedSeries.flipLabel n)‖ =
      ‖(pairedCarrierCoefficients A B L₁ L₂ hA hB).coeff D n‖ :=
  PairedSeries.coefficient_norm_flip (A D) (B D) n

def pairedAtom (R : E →L[ℝ] E) (atom : ℕ → E) (n : ℕ) : E :=
  Sum.elim atom (fun m => R (atom m)) (PairedSeries.labels.symm n)

@[simp] theorem pairedAtom_left (R : E →L[ℝ] E) (atom : ℕ → E) (n : ℕ) :
    pairedAtom R atom (PairedSeries.labels (Sum.inl n)) = atom n := by
  simp only [pairedAtom, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem pairedAtom_right (R : E →L[ℝ] E) (atom : ℕ → E) (n : ℕ) :
    pairedAtom R atom (PairedSeries.labels (Sum.inr n)) = R (atom n) := by
  simp only [pairedAtom, Equiv.symm_apply_apply, Sum.elim_inr]

theorem pairedAtom_reflection (R : E →L[ℝ] E) (hR : ∀ x, R (R x) = x) (atom : ℕ → E) (n : ℕ) :
    R (pairedAtom R atom n) = pairedAtom R atom (PairedSeries.flipLabel n) := by
  obtain ⟨s, rfl⟩ := PairedSeries.labels.surjective n
  cases s <;> simp only [PairedSeries.flipLabel_left, PairedSeries.flipLabel_right,
    pairedAtom_left, pairedAtom_right, hR]

theorem pairedAtom_bound (R : E →L[ℝ] E) (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    (e : E) (he : R e = e) (atom : ℕ → E) (M : ℝ) (ha : ∀ n, ‖atom n - e‖ ≤ M) (n : ℕ) :
    ‖pairedAtom R atom n - e‖ ≤ M := by
  unfold pairedAtom
  cases PairedSeries.labels.symm n with
  | inl m => exact ha m
  | inr m =>
    calc
      ‖R (atom m) - e‖ = ‖R (atom m - e)‖ := by rw [map_sub, he]
      _ ≤ ‖atom m - e‖ := hR _
      _ ≤ M := ha m

def firstEvaluation (ev : V →ₗ[ℝ] ℝ) : (V × V) →ₗ[ℝ] ℝ := ev.comp (LinearMap.fst ℝ V V)

@[simp] theorem firstEvaluation_apply (ev : V →ₗ[ℝ] ℝ) (a : V × V) : firstEvaluation ev a = ev a.1 := rfl

theorem firstEvaluation_bound (ev : V →ₗ[ℝ] ℝ) (hev : ∀ a, |ev a| ≤ ‖a‖) (a : V × V) :
    |firstEvaluation ev a| ≤ ‖a‖ := (hev a.1).trans (norm_fst_le a)

theorem pairedCoefficient_reconstruction {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b : VectorSeries.Family ℕ V) (ev : V →ₗ[ℝ] ℝ) (f g : ℕ → F) (t : F)
    (ha : HasSum (fun n => ev (a n) • f n) t) (hb : HasSum (fun n => ev (b n) • g n) t) :
    HasSum (fun n => firstEvaluation ev (PairedSeries.family a b n) •
      Sum.elim f g (PairedSeries.labels.symm n)) t := by
  have hr : HasSum (Sum.elim (fun n => (1 / 2 : ℝ) • (ev (a n) • f n))
      (fun n => (1 / 2 : ℝ) • (ev (b n) • g n))) ((1 / 2 : ℝ) • t + (1 / 2 : ℝ) • t) :=
    HasSum.sum (f := Sum.elim (fun n => (1 / 2 : ℝ) • (ev (a n) • f n))
      (fun n => (1 / 2 : ℝ) • (ev (b n) • g n)))
      (ha.const_smul (1 / 2 : ℝ)) (hb.const_smul (1 / 2 : ℝ))
  have he : (1 / 2 : ℝ) • t + (1 / 2 : ℝ) • t = t := by rw [← add_smul]; norm_num
  rw [he] at hr
  have hn := (PairedSeries.labels.symm.hasSum_iff
    (f := Sum.elim (fun n => (1 / 2 : ℝ) • (ev (a n) • f n))
      (fun n => (1 / 2 : ℝ) • (ev (b n) • g n)))).mpr hr
  apply hn.congr_fun
  intro n
  simp only [Function.comp_def, firstEvaluation_apply, PairedSeries.family_apply, PairedSeries.coefficient]
  cases PairedSeries.labels.symm n <;>
    simp only [Sum.elim_inl, Sum.elim_inr, Prod.smul_fst, map_smul, smul_eq_mul, smul_smul]

end CausalLowerbound.PartC

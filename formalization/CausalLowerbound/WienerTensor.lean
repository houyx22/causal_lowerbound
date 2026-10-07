import CausalLowerbound.WienerAlgebra
import CausalLowerbound.PartB.PolarizationAlgebra

/-! # Products in distinct torus slots and their Wiener norm -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open UnitAddTorus

namespace CausalLowerbound.Wiener

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d]

def slotFrequency (i : ι) (k : d → ℤ) : (ι × d) → ℤ :=
  fun p => if p.1 = i then k p.2 else 0

theorem slotFrequency_character (i : ι) (k : d → ℤ) (x : Torus (ι × d)) :
    mFourier (slotFrequency i k) x = mFourier k (fun j => x (i, j)) := by
  simp only [mFourier, ContinuousMap.coe_mk, Fintype.prod_prod_type, slotFrequency]
  rw [Finset.prod_eq_single i]
  · simp
  · intro a _ ha
    simp [ha, fourier_zero]
  · simp

def liftSlot (i : ι) : Fourier d →L[ℂ] Fourier (ι × d) := regroup (slotFrequency i)

theorem liftSlot_norm (i : ι) (a : Fourier d) : ‖liftSlot i a‖ ≤ ‖a‖ :=
  regroup_bound _ a

theorem liftSlot_value (i : ι) (a : Fourier d) (x : Torus (ι × d)) :
    toContinuous (liftSlot i a) x = toContinuous a (fun j => x (i, j)) := by
  change synthesis mFourier 1 (fun _ => mFourier_norm.le)
    (regroup (slotFrequency i) a) x = _
  rw [synthesis_regroup]
  have h := (ContinuousMap.evalCLM ℂ x).map_tsum
    (summable_synthesis (fun k => mFourier (slotFrequency i k)) 1
      (fun _ => mFourier_norm.le) a)
  have h' := (ContinuousMap.evalCLM ℂ (fun j => x (i, j))).map_tsum
    (summable_synthesis mFourier 1 (fun _ => mFourier_norm.le) a)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, slotFrequency_character] at h h'
  exact h.trans h'.symm

def tensor (f : ι → Fourier d) : Fourier (ι × d) := ∏ i, liftSlot i (f i)

theorem toContinuous_prod {α : Type*} (s : Finset α) (f : α → Fourier d) :
    toContinuous (∏ i ∈ s, f i) = ∏ i ∈ s, toContinuous (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.prod_insert hi, ih]

theorem tensor_value (f : ι → Fourier d) (x : Torus (ι × d)) :
    toContinuous (tensor f) x = ∏ i, toContinuous (f i) (fun j => x (i, j)) := by
  simp only [tensor, toContinuous_prod, ContinuousMap.prod_apply, liftSlot_value]

theorem tensor_norm (f : ι → Fourier d) : ‖tensor f‖ ≤ ∏ i, ‖f i‖ := by
  change ‖∏ i : ι, liftSlot i (f i)‖ ≤ _
  calc
    _ ≤ ∏ i, ‖liftSlot i (f i)‖ := Finset.norm_prod_le Finset.univ (fun i : ι => liftSlot i (f i))
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => liftSlot_norm i (f i))

def symTensor (f : ι → Fourier d) : Fourier (ι × d) :=
  (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ • ∑ σ : Equiv.Perm ι, tensor (fun i => f (σ i))

theorem symTensor_norm (f : ι → Fourier d) (hf : ∀ i, ‖f i‖ ≤ 1) : ‖symTensor f‖ ≤ 1 := by
  have hn : 0 < (Fintype.card (Equiv.Perm ι) : ℝ) := by exact_mod_cast Fintype.card_pos
  have ht (σ : Equiv.Perm ι) : ‖tensor (fun i => f (σ i))‖ ≤ 1 := by
    calc
      _ ≤ ∏ i, ‖f (σ i)‖ := tensor_norm _
      _ ≤ ∏ _i : ι, (1 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hf (σ i))
      _ = 1 := by simp
  rw [symTensor, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ * ∑ σ : Equiv.Perm ι,
        ‖tensor (fun i => f (σ i))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ * ∑ _σ : Equiv.Perm ι, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ht σ) (inv_nonneg.mpr hn.le)
    _ = 1 := by simp [hn.ne']

theorem symTensor_value (f : ι → Fourier d) (x : Torus (ι × d)) :
    toContinuous (symTensor f) x =
      (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ •
        ∑ σ : Equiv.Perm ι, ∏ i, toContinuous (f (σ i)) (fun j => x (i, j)) := by
  have h := ((toContinuous (d := ι × d)).restrictScalars ℝ).map_smul
    (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹
    (∑ σ : Equiv.Perm ι, tensor (fun i => f (σ i)))
  change toContinuous ((Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ •
    ∑ σ : Equiv.Perm ι, tensor (fun i => f (σ i))) =
      (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ •
        toContinuous (∑ σ : Equiv.Perm ι, tensor (fun i => f (σ i))) at h
  change toContinuous (symTensor f) x = _
  simp only [symTensor, h, map_sum, ContinuousMap.smul_apply, ContinuousMap.sum_apply, tensor_value]

end CausalLowerbound.Wiener

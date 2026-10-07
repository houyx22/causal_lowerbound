import CausalLowerbound.PartC.RepresentativeSubstitution
import CausalLowerbound.WienerRealExpansion

/-! Simultaneous permutation of retained Fourier coordinates and degree
rows. Symmetrization is an actual contraction of the representative space,
so it does not rely on injectivity of physical realization. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC.Representative

open Wiener UnitAddTorus
variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

def permutedFrequency (σ : Equiv.Perm ι) (k : ι × d → ℤ) : ι × d → ℤ :=
  fun p => k (σ.symm p.1, p.2)

theorem permutedFrequency_character (σ : Equiv.Perm ι) (k : ι × d → ℤ) (x : Torus (ι × d)) :
    mFourier (permutedFrequency σ k) x = mFourier k (permuteSlots σ x) := by
  simp only [character_slots, permutedFrequency, permuteSlots]
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.prod_comp σ (fun i => mFourier (fun j => k (σ.symm i, j)) (fun j => x (i, j)))).symm

def fourierPermutation (σ : Equiv.Perm ι) : Fourier (ι × d) →L[ℂ] Fourier (ι × d) :=
  regroup (permutedFrequency σ)

theorem fourierPermutation_bound (σ : Equiv.Perm ι) (a : Fourier (ι × d)) :
    ‖fourierPermutation σ a‖ ≤ ‖a‖ := regroup_bound _ a

theorem fourierPermutation_value (σ : Equiv.Perm ι) (a : Fourier (ι × d)) (x : Torus (ι × d)) :
    toContinuous (fourierPermutation σ a) x = toContinuous a (permuteSlots σ x) := by
  change synthesis mFourier 1 (fun _ => mFourier_norm.le) (regroup (permutedFrequency σ) a) x = _
  rw [synthesis_regroup]
  have h := (ContinuousMap.evalCLM ℂ x).map_tsum
    (summable_synthesis (fun k => mFourier (permutedFrequency σ k)) 1 (fun _ => mFourier_norm.le) a)
  have h' := (ContinuousMap.evalCLM ℂ (permuteSlots σ x)).map_tsum
    (summable_synthesis mFourier 1 (fun _ => mFourier_norm.le) a)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, permutedFrequency_character] at h h'
  exact h.trans h'.symm

def permutedRow (σ : Equiv.Perm ι) (r : Row ι J D) : Row ι J D :=
  (fun i => r.1 (σ.symm i), r.2)

theorem permutedRow_weight (σ : Equiv.Perm ι) (r : Row ι J D) (z : ι → ℝ) (ζ : J → Bool) :
    rowWeight (permutedRow σ r) z ζ = rowWeight r (fun i => z (σ i)) ζ := by
  unfold rowWeight monomial permutedRow
  congr 1
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.prod_comp σ (fun i => z i ^ (r.1 (σ.symm i)).val)).symm

def permutation (σ : Equiv.Perm ι) : Array d ι J D →L[ℝ] Array d ι J D :=
  FiniteL1.transform (permutedRow σ) (fun _ => (fourierPermutation σ).restrictScalars ℝ) 1
    (fun _ a => by simpa only [one_mul] using fourierPermutation_bound σ a)

theorem permutation_bound (σ : Equiv.Perm ι) (a : Array d ι J D) : ‖permutation σ a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using FiniteL1.transform_bound (permutedRow σ)
    (fun _ => (fourierPermutation σ).restrictScalars ℝ) 1
      (fun _ a => by simpa only [one_mul] using fourierPermutation_bound σ a) a

theorem permutation_single (σ : Equiv.Perm ι) (r : Row ι J D) (a : Fourier (ι × d)) :
    permutation σ (lp.single 1 r a) = lp.single 1 (permutedRow σ r) (fourierPermutation σ a) :=
  FiniteL1.transform_single _ _ 1 _ r a

theorem permutation_value (σ : Equiv.Perm ι) (a : Array d ι J D)
    (x : Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool) :
    pointValue x z ζ (permutation σ a) = pointValue (permuteSlots σ x) (fun i => z (σ i)) ζ a := by
  rw [← FiniteL1.sum_single a]
  simp only [map_sum, permutation_single, pointValue_sum, pointValue_single,
    fourierPermutation_value, permutedRow_weight]

theorem permutation_symbolProject (σ : Equiv.Perm ι) (a : Array d ι J D)
    (p : Finset J → Prop) [DecidablePred p] :
    FiniteL1.project (fun r : Row ι J D => p r.2) (permutation σ a) =
      permutation σ (FiniteL1.project (fun r : Row ι J D => p r.2) a) := by
  rw [← FiniteL1.sum_single a]
  simp only [map_sum, permutation_single, symbolProject_single]
  apply Finset.sum_congr rfl
  intro r _
  change (lp.single 1 (permutedRow σ r) (if p r.2 then fourierPermutation σ (a r) else 0) : Array d ι J D) = _
  split_ifs <;> simp only [map_zero]

def symmetrize : Array d ι J D →L[ℝ] Array d ι J D :=
  (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ • ∑ σ : Equiv.Perm ι, permutation (d := d) (J := J) (D := D) σ

theorem symmetrize_bound (a : Array d ι J D) : ‖symmetrize a‖ ≤ ‖a‖ := by
  have hn : 0 < (Fintype.card (Equiv.Perm ι) : ℝ) := by exact_mod_cast Fintype.card_pos
  simp only [symmetrize, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ * ∑ σ : Equiv.Perm ι, ‖permutation σ a‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ * ∑ _σ : Equiv.Perm ι, ‖a‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun σ _ => permutation_bound σ a)) (inv_nonneg.mpr hn.le)
    _ = ‖a‖ := by simp [hn.ne', ← mul_assoc]

theorem symmetrize_value (a : Array d ι J D) (x : Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool) :
    pointValue x z ζ (symmetrize a) = (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm ι, pointValue (permuteSlots σ x) (fun i => z (σ i)) ζ a := by
  simp only [symmetrize, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    pointValue_smul, pointValue_sum, permutation_value, smul_eq_mul]

theorem symmetrize_value_symmetric (a : Array d ι J D) (x : Torus (ι × d))
    (z : ι → ℝ) (ζ : J → Bool) (σ : Equiv.Perm ι) :
    pointValue (permuteSlots σ x) (fun i => z (σ i)) ζ (symmetrize a) = pointValue x z ζ (symmetrize a) := by
  rw [symmetrize_value, symmetrize_value]
  congr 1
  simpa only [Equiv.coe_mulLeft, Equiv.Perm.coe_mul, Function.comp_apply, permuteSlots] using
    (Equiv.sum_comp (Equiv.mulLeft σ) (fun τ : Equiv.Perm ι =>
      pointValue (permuteSlots τ x) (fun i => z (τ i)) ζ a))

theorem symmetrize_symbolProject (a : Array d ι J D) (p : Finset J → Prop) [DecidablePred p] :
    FiniteL1.project (fun r : Row ι J D => p r.2) (symmetrize a) =
      symmetrize (FiniteL1.project (fun r : Row ι J D => p r.2) a) := by
  simp only [symmetrize, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    map_smul, map_sum, permutation_symbolProject]

end CausalLowerbound.PartC.Representative

import CausalLowerbound.PartC.RepresentativeTensor

/-! Symmetrized cross-slot tensors retain the full representative arrays. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC.Representative

open PartB.Polarization

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

def symTensor (f : ι → Factor d J D) : Array d ι J D :=
  (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ • ∑ σ : Equiv.Perm ι, tensor (fun i => f (σ i))

theorem symTensor_norm (f : ι → Factor d J D) : ‖symTensor f‖ ≤ ∏ i, ‖f i‖ := by
  have hn : 0 < (Fintype.card (Equiv.Perm ι) : ℝ) := by exact_mod_cast Fintype.card_pos
  have ht (σ : Equiv.Perm ι) : ‖tensor (fun i => f (σ i))‖ ≤ ∏ i, ‖f i‖ :=
    (tensor_norm _).trans_eq (Equiv.prod_comp σ (fun i => ‖f i‖))
  rw [symTensor, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  calc
    _ ≤ (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ * ∑ σ : Equiv.Perm ι, ‖tensor (fun i => f (σ i))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ * ∑ _σ : Equiv.Perm ι, ∏ i, ‖f i‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun σ _ => ht σ)) (inv_nonneg.mpr hn.le)
    _ = ∏ i, ‖f i‖ := by simp [hn.ne']

theorem symTensor_value (f : ι → Factor d J D) (x : Wiener.Torus (ι × d)) (z : ι → ℝ)
    (ζ : J → Bool) (hreal : ∀ i y t, (factorValue y t ζ (f i)).im = 0) :
    pointValue x z ζ (symTensor f) =
      symProduct (fun i (p : Wiener.Torus d × ℝ) => (factorValue p.1 p.2 ζ (f i)).re)
        (fun i => (fun j => x (i, j), z i)) := by
  simp only [symTensor, pointValue_smul, pointValue_sum, smul_eq_mul]
  have hv (σ : Equiv.Perm ι) : pointValue x z ζ (tensor (fun i => f (σ i))) =
      ∏ i, (factorValue (fun j => x (i, j)) (z i) ζ (f (σ i))).re :=
    tensor_value_real _ x z ζ (fun i => hreal (σ i) _ _)
  simp_rw [hv]
  rfl

end CausalLowerbound.PartC.Representative

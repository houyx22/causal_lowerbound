import CausalLowerbound.UpperBound.ObservedFeatures
import Mathlib.Algebra.Order.Ring.Abs

/-! Quantitative variation of the fixed tensor feature vector on the unit
cube.  These bounds are applied to the observed inward coordinates. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {I : Type*}

theorem abs_prod_sub_prod_le_sum (s : Finset I) (a b : I → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have ha' := fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have hb' := fun j hj => hb j (Finset.mem_insert_of_mem hj)
      have hp : |∏ j ∈ s, b j| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun _ _ => abs_nonneg _) hb'
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
      calc
        _ = |a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) +
            (a i - b i) * ∏ j ∈ s, b j| := by congr 1; ring
        _ ≤ |a i| * |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| +
            |a i - b i| * |∏ j ∈ s, b j| := by
              rw [← abs_mul, ← abs_mul]
              exact abs_add_le _ _
        _ ≤ (∑ j ∈ s, |a j - b j|) + |a i - b i| := add_le_add
          ((mul_le_of_le_one_left (abs_nonneg _) (ha i (Finset.mem_insert_self _ _))).trans (ih ha' hb'))
          (mul_le_of_le_one_right (abs_nonneg _) hp)
        _ = _ := add_comm _ _

theorem abs_pow_sub_pow_le_of_abs_le_one (a b : ℝ) (n : ℕ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a ^ n - b ^ n| ≤ n * |a - b| := by
  have hp : max |a| |b| ^ (n - 1) ≤ 1 :=
    pow_le_one₀ (le_max_of_le_left (abs_nonneg _)) (max_le ha hb)
  exact (abs_pow_sub_pow_le a b n).trans
    ((mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) hp).trans_eq (mul_comm _ _))

variable {d : Type*} [Fintype d]

theorem tensorMonomial_lipschitz (p : ℕ) (ν : TensorIndex d p) (u v : d → ℝ)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    |tensorMonomial p ν u - tensorMonomial p ν v| ≤
      (Fintype.card d * p : ℝ) * ‖u - v‖ := by
  have hua (i : d) : |u i| ≤ 1 := (norm_le_pi_norm u i).trans hu
  have hva (i : d) : |v i| ≤ 1 := (norm_le_pi_norm v i).trans hv
  calc
    _ ≤ ∑ i : d, |u i ^ (ν i : ℕ) - v i ^ (ν i : ℕ)| :=
      abs_prod_sub_prod_le_sum Finset.univ _ _
        (fun i _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hua i))
        (fun i _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hva i))
    _ ≤ ∑ _i : d, (p : ℝ) * ‖u - v‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply (abs_pow_sub_pow_le_of_abs_le_one (u i) (v i) (ν i) (hua i) (hva i)).trans
      have hi : ((ν i : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast Nat.le_of_lt_succ (ν i).isLt
      exact mul_le_mul hi
        (norm_le_pi_norm (u - v) i) (abs_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by simp [mul_assoc]

theorem normalizedDisplacement_sub_norm (x₀ origin x y : d → ℝ) {h : ℝ} (hh : 0 < h) :
    ‖normalizedDisplacement x₀ origin x h - normalizedDisplacement x₀ origin y h‖ =
      h⁻¹ * ‖x - y‖ := by
  change ‖h⁻¹ • inwardReflectionL x₀ (x - origin) -
    h⁻¹ • inwardReflectionL x₀ (y - origin)‖ = _
  rw [← smul_sub, ← map_sub]
  have he : x - origin - (y - origin) = x - y := by abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh,
    inwardReflectionL_apply, inwardReflection_norm]

theorem acceptedStencil_feature_difference (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (X : StencilRole d p → d → ℝ) (hX : X ∈ acceptedStencil p T x₀ h ℓ r)
    (i j : StencilRole d p) (ν : TensorIndex d p) :
    |stencilFeature p x₀ h X i ν - stencilFeature p x₀ h X j ν| ≤
      (Fintype.card d * p : ℝ) * (h⁻¹ * ‖X i - X j‖) := by
  have he := tensorMonomial_lipschitz p ν _ _
    (acceptedStencil_displacement_norm_le p T x₀ hx hh hhsmall hℓ hℓr hrh X hX i)
    (acceptedStencil_displacement_norm_le p T x₀ hx hh hhsmall hℓ hℓr hrh X hX j)
  rwa [normalizedDisplacement_sub_norm x₀ x₀ _ _ hh] at he

end CausalLowerbound.UpperBound

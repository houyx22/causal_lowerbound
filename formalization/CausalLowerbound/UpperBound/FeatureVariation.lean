import CausalLowerbound.UpperBound.FeatureLipschitz
import CausalLowerbound.UpperBound.ScoreBias

/-! Weighted variation from the anchor is of order ell/h.  This controls
both the absolute-weight and squared-weight feature averages. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

theorem distance_le_of_normalizedDisplacement (x₀ origin y : d → ℝ)
    {r : ℝ} (hr : 0 < r) (hy : ‖normalizedDisplacement x₀ origin y r‖ ≤ 1) :
    ‖y - origin‖ ≤ r := by
  have he := normalizedDisplacement_reconstruct x₀ origin y r hr.ne'
  have hd : y - origin = r • inwardReflection x₀ (normalizedDisplacement x₀ origin y r) := by
    exact (eq_sub_of_add_eq' he).symm
  rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos hr, inwardReflection_norm]
  exact (mul_le_mul_of_nonneg_left hy hr.le).trans_eq (mul_one _)

theorem acceptedStencil_partner_distance (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hℓ : 0 < ℓ)
    (X : StencilRole d p → d → ℝ) (hX : X ∈ acceptedStencil p T x₀ h ℓ r) :
    ‖X none - X (some none)‖ ≤ ℓ :=
  distance_le_of_normalizedDisplacement x₀ _ _ hℓ
    (nonnegative_coordinate_norm_le zero_le_one (fun a => ⟨hX.2.1.1 a, hX.2.1.2 a⟩))

theorem acceptedStencil_auxiliary_distance (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hr : 0 < r)
    (X : StencilRole d p → d → ℝ) (hX : X ∈ acceptedStencil p T x₀ h ℓ r)
    (j : TensorIndex d p) : ‖X (some (some j)) - X (some none)‖ ≤ r :=
  distance_le_of_normalizedDisplacement x₀ _ _ hr
    (nonnegative_coordinate_norm_le zero_le_one (fun a =>
      ⟨(T.box_positive j (hX.2.2 j) a).1.le, (T.box_positive j (hX.2.2 j) a).2.le⟩))

theorem acceptedStencil_auxiliary_weight (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r)
    (X : StencilRole d p → d → ℝ) (hX : X ∈ acceptedStencil p T x₀ h ℓ r)
    (j : TensorIndex d p) :
    |observedStencilWeights p x₀ ℓ r X (some (some j))| ≤ T.inverseBound * (ℓ / r) := by
  have hr : 0 < r := hℓ.trans_le hℓr
  have hη : 0 ≤ ℓ / r := div_nonneg hℓ.le hr.le
  apply tensorContrastWeights_auxiliary_bound p _ _
    (T.valid_of_mem_boxes _ hX.2.2).2.2 hη ((div_le_one hr).mpr hℓr)
  intro a
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hη,
    abs_of_nonneg (hX.2.1.1 a)]
  exact (mul_le_mul_of_nonneg_left (hX.2.1.2 a) hη).trans_eq (mul_one _)

def stencilFeatureVariationBound (p : ℕ) (T : StencilTemplate d p) (h ℓ : ℝ) : ℝ :=
  (Fintype.card d * p : ℝ) * (1 + Fintype.card (TensorIndex d p) * T.inverseBound) * (ℓ / h)

theorem stencilFeatureVariationBound_nonneg (p : ℕ) (T : StencilTemplate d p)
    {h ℓ : ℝ} (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ) : 0 ≤ stencilFeatureVariationBound p T h ℓ := by
  have hi := T.inverseBound_pos.le
  unfold stencilFeatureVariationBound
  positivity

theorem acceptedStencil_feature_variation (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (X : StencilRole d p → d → ℝ) (hX : X ∈ acceptedStencil p T x₀ h ℓ r)
    (ν : TensorIndex d p) :
    (∑ i, |observedStencilWeights p x₀ ℓ r X i| *
      |stencilFeature p x₀ h X i ν - stencilFeature p x₀ h X (some none) ν|) ≤
        stencilFeatureVariationBound p T h ℓ := by
  let D : ℝ := Fintype.card d * p
  have hD : 0 ≤ D := by positivity
  have hr : 0 < r := hℓ.trans_le hℓr
  have hp : |stencilFeature p x₀ h X none ν - stencilFeature p x₀ h X (some none) ν| ≤ D * (ℓ / h) := by
    apply (acceptedStencil_feature_difference p T x₀ hx hh hhsmall hℓ hℓr hrh X hX none (some none) ν).trans
    have he := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (acceptedStencil_partner_distance p T x₀ hℓ X hX) (inv_nonneg.mpr hh.le)) hD
    simpa only [D, div_eq_mul_inv, mul_comm] using he
  have ha (j : TensorIndex d p) :
      |stencilFeature p x₀ h X (some (some j)) ν - stencilFeature p x₀ h X (some none) ν| ≤ D * (r / h) := by
    apply (acceptedStencil_feature_difference p T x₀ hx hh hhsmall hℓ hℓr hrh X hX _ _ ν).trans
    have he := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (acceptedStencil_auxiliary_distance p T x₀ hr X hX j) (inv_nonneg.mpr hh.le)) hD
    simpa only [D, div_eq_mul_inv, mul_comm] using he
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [sub_self, abs_zero, mul_zero, zero_add]
  calc
    _ ≤ D * (ℓ / h) + ∑ _j : TensorIndex d p, T.inverseBound * D * (ℓ / h) := by
      apply add_le_add
      · exact (mul_le_of_le_one_left (abs_nonneg _)
          (normalized_weight_abs_le_one _ (observedStencilWeights_norm_sq p x₀ ℓ r X) none)).trans hp
      · apply Finset.sum_le_sum
        intro j _
        apply (mul_le_mul (acceptedStencil_auxiliary_weight p T x₀ hℓ hℓr X hX j) (ha j)
          (abs_nonneg _) (mul_nonneg T.inverseBound_pos.le (div_nonneg hℓ.le hr.le))).trans_eq
        field_simp [hr.ne']
        <;> ring
    _ = _ := by simp [stencilFeatureVariationBound, D]; ring

variable {I : Type*} [Fintype I]

theorem squared_weight_variation_le (w φ : I → ℝ) (a : ℝ)
    (hw : ∑ i, w i ^ 2 = 1) :
    (∑ i, w i ^ 2 * |φ i - a|) ≤ ∑ i, |w i| * |φ i - a| := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have he := normalized_weight_abs_le_one w hw i
  calc
    w i ^ 2 = |w i| * |w i| := by rw [← pow_two, sq_abs]
    _ ≤ |w i| := mul_le_of_le_one_right (abs_nonneg _) he

theorem squared_weight_mean_difference (w φ : I → ℝ) (a : ℝ)
    (hw : ∑ i, w i ^ 2 = 1) :
    |(∑ i, w i ^ 2 * φ i) - a| ≤ ∑ i, |w i| * |φ i - a| := by
  have he : (∑ i, w i ^ 2 * φ i) - a = ∑ i, w i ^ 2 * (φ i - a) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul]
  rw [he]
  calc
    _ ≤ ∑ i, |w i ^ 2 * (φ i - a)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i ^ 2 * |φ i - a| := by simp only [abs_mul, abs_sq]
    _ ≤ _ := squared_weight_variation_le w φ a hw

end CausalLowerbound.UpperBound

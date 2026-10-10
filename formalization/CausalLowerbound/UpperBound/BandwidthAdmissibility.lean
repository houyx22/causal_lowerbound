import CausalLowerbound.UpperBound.MasterEnvelope
import CausalLowerbound.UpperBound.PolynomialBandwidth

/-! Explicit coarse-scale budget and eventual geometric/matrix admissibility
for polynomial bandwidths.  The eventual index is uniform over the model
and target, since all conditions involve class parameters only. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

def stencilCoarseBudget (p : ℕ) (T : StencilTemplate d p) (upper : ℝ) : ℝ :=
  max 1 (max upper (4 * Fintype.card (StencilRole d p) / (2 * T.radius) ^ Fintype.card d))

theorem stencilCoarseBudget_one_le (p : ℕ) (T : StencilTemplate d p) (upper : ℝ) :
    1 ≤ stencilCoarseBudget p T upper := le_max_left _ _

theorem stencilCoarseBudget_upper_le (p : ℕ) (T : StencilTemplate d p) (upper : ℝ) :
    upper ≤ stencilCoarseBudget p T upper := (le_max_left _ _).trans (le_max_right _ _)

theorem coarseCellVolume_polynomial [Nonempty d] (p : ℕ) (T : StencilTemplate d p) (n : ℕ) :
    (coarseCellVolume p T (polynomialBandwidth (1 / Fintype.card d) n)).toReal =
      (2 * T.radius) ^ Fintype.card d * polynomialBandwidth 1 n := by
  have hr := polynomialBandwidth_pos (1 / Fintype.card d) n
  have hδ := T.radius_pos
  have hD : (Fintype.card d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos (α := d)))
  unfold coarseCellVolume
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
    show 2 * polynomialBandwidth (1 / Fintype.card d) n * T.radius =
      (2 * T.radius) * polynomialBandwidth (1 / Fintype.card d) n by ring,
    mul_pow, polynomialBandwidth_pow, div_mul_cancel₀ _ hD]

theorem stencilCoarseBudget_group_bound [Nonempty d] (p : ℕ) (T : StencilTemplate d p)
    (upper : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    2 * Fintype.card (StencilRole d p) / (n : ℝ) ≤ stencilCoarseBudget p T upper *
      (coarseCellVolume p T (polynomialBandwidth (1 / Fintype.card d) n)).toReal := by
  have hδ := T.radius_pos
  have hC : (0 : ℝ) < (2 * T.radius) ^ Fintype.card d := by positivity
  have hb : 4 * Fintype.card (StencilRole d p) / (2 * T.radius) ^ Fintype.card d ≤
      stencilCoarseBudget p T upper := (le_max_right _ _).trans (le_max_right _ _)
  have hb' := (div_le_iff₀ hC).mp hb
  have he := mul_le_mul_of_nonneg_left (reciprocal_sampleSize_le_bandwidth hn)
    (show (0 : ℝ) ≤ 2 * Fintype.card (StencilRole d p) by positivity)
  rw [coarseCellVolume_polynomial]
  calc
    _ ≤ (4 * Fintype.card (StencilRole d p)) * polynomialBandwidth 1 n := by
      convert he using 1 <;> ring
    _ ≤ (stencilCoarseBudget p T upper * (2 * T.radius) ^ Fintype.card d) * polynomialBandwidth 1 n :=
      mul_le_mul_of_nonneg_right hb' (polynomialBandwidth_pos _ _).le
    _ = _ := by ring

theorem stencilNuisanceBound_polynomial_tendsto (p : ℕ) (T : StencilTemplate d p)
    {α b c : ℝ} (L : ℝ) (hα : 0 < α) (hb : 0 < b) (hc : 0 ≤ c) :
    Tendsto (fun n => stencilNuisanceBound p T α L (polynomialBandwidth b n) (polynomialBandwidth c n))
      atTop (𝓝 0) := by
  simpa only [stencilNuisanceBound, mul_zero] using
    (twoScaleModulus_polynomial_tendsto hα hb hc).const_mul
      (L * (1 + Fintype.card (TensorIndex d p) * T.inverseBound))

theorem stencilFeatureVariation_polynomial_tendsto (p : ℕ) (T : StencilTemplate d p)
    {a b : ℝ} (hab : a < b) :
    Tendsto (fun n => stencilFeatureVariationBound p T (polynomialBandwidth a n) (polynomialBandwidth b n))
      atTop (𝓝 0) := by
  simpa only [stencilFeatureVariationBound, mul_zero] using
    (polynomialBandwidth_div_tendsto hab).const_mul
      ((Fintype.card d * p : ℝ) * (1 + Fintype.card (TensorIndex d p) * T.inverseBound))

theorem stencilMatrixError_polynomial_tendsto (p : ℕ) (T : StencilTemplate d p)
    {α a b c : ℝ} (L upper : ℝ) (hα : 0 < α) (hb : 0 < b) (hc : 0 ≤ c) (hab : a < b) :
    Tendsto (fun n => stencilMatrixErrorSize p T α L upper
      (polynomialBandwidth a n) (polynomialBandwidth b n) (polynomialBandwidth c n)) atTop (𝓝 0) := by
  have hA := stencilNuisanceBound_polynomial_tendsto p T L hα hb hc
  have hV := stencilFeatureVariation_polynomial_tendsto p T hab
  have he := (((hA.mul (hA.add hV)).add (hV.const_mul 2)).mul_const
    (upper ^ Fintype.card (StencilRole d p))).const_mul (Fintype.card (TensorIndex d p) : ℝ)
  simpa only [stencilMatrixErrorSize, add_zero, zero_add, mul_zero, zero_mul] using he

theorem eventually_polynomial_geometry {a b c : ℝ} (ha : 0 < a) (hac : a < c) (hcb : c ≤ b) :
    ∀ᶠ n in atTop,
      0 < polynomialBandwidth a n ∧ polynomialBandwidth a n ≤ 1 / 2 ∧
      0 < polynomialBandwidth b n ∧ polynomialBandwidth b n ≤ polynomialBandwidth c n ∧
      polynomialBandwidth c n ≤ polynomialBandwidth a n / 4 := by
  have hh := (polynomialBandwidth_tendsto ha).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hr := (polynomialBandwidth_div_tendsto hac).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hh, hr] with n hn hn'
  refine ⟨polynomialBandwidth_pos _ _, hn.le, polynomialBandwidth_pos _ _, polynomialBandwidth_antitone hcb n, ?_⟩
  have he := (div_le_iff₀ (polynomialBandwidth_pos a n)).mp hn'.le
  linarith

theorem eventually_polynomial_matrix_small (p : ℕ) (T : StencilTemplate d p)
    {α a b c κ : ℝ} (L upper : ℝ) (hα : 0 < α) (hb : 0 < b) (hc : 0 ≤ c)
    (hab : a < b) (hκ : 0 < κ) :
    ∀ᶠ n in atTop, stencilMatrixErrorSize p T α L upper
      (polynomialBandwidth a n) (polynomialBandwidth b n) (polynomialBandwidth c n) ≤ 2 * κ := by
  exact ((stencilMatrixError_polynomial_tendsto p T L upper hα hb hc hab).eventually
    (gt_mem_nhds (by positivity : 0 < 2 * κ))).mono (fun _ hn => hn.le)

end CausalLowerbound.UpperBound

import CausalLowerbound.PartB.BlockIndependence

/-! The posterior of the real carrier labels after observing the design.
Its product structure is a consequence of the Z^n cancellation and Bayes'
formula, not an independence assumption on the mixed design sample. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

def sitesCarrierFactor (Q : ℕ) (θ : ℝ) (x₀ : d → ℝ) (r : ℝ) {n : ℕ}
    (x : Fin n → d → ℝ) (k : d → ℤ) (label : ℕ) : ℝ :=
  ∏ i, physicalFactor Q θ label x₀ r k (x i)

theorem sitesCarrierFactor_bounds (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x₀ : d → ℝ) (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) (k : d → ℤ) (label : ℕ) :
    (1 - θ) ^ n ≤ sitesCarrierFactor Q θ x₀ r x k label ∧
      sitesCarrierFactor Q θ x₀ r x k label ≤ (1 + θ) ^ n := by
  have h0 : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1.le
  constructor
  · simpa [sitesCarrierFactor] using Finset.prod_le_prod (s := Finset.univ)
      (f := fun _ : Fin n => 1 - θ) (fun _ _ => h0)
      (fun i _ => (physicalFactor_bounds Q θ hθ label x₀ r k (x i)).1)
  · simpa [sitesCarrierFactor] using Finset.prod_le_prod (s := Finset.univ)
      (f := fun i : Fin n => physicalFactor Q θ label x₀ r k (x i))
      (fun i _ => h0.trans (physicalFactor_bounds Q θ hθ label x₀ r k (x i)).1)
      (fun i _ => (physicalFactor_bounds Q θ hθ label x₀ r k (x i)).2)

theorem design_sample_factorization (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (labels : S → ℕ) (x₀ : d → ℝ) (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) :
    (∏ i, unnormalizedDesign Q S θ (extendLabels S labels) x₀ r (x i)) =
      ∏ k : S, sitesCarrierFactor Q θ x₀ r x k.val (labels k) := by
  have he (i : Fin n) : unnormalizedDesign Q S θ (extendLabels S labels) x₀ r (x i) =
      ∏ k : S, physicalFactor Q θ (labels k) x₀ r k.val (x i) := by
    unfold unnormalizedDesign
    rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro k _
    simp only [extendLabels, dif_pos k.property]
  simp only [he, sitesCarrierFactor]
  exact Finset.prod_comm

def posteriorLabelLaw (H : DiscreteLaw ℕ) (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x₀ : d → ℝ) (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) (k : d → ℤ) : DiscreteLaw ℕ :=
  H.tilt (sitesCarrierFactor Q θ x₀ r x k) ((1 - θ) ^ n) ((1 + θ) ^ n)
    (pow_pos (sub_pos.mpr hθ1) _) (sitesCarrierFactor_bounds Q θ hθ hθ1 x₀ r x k)

def designPosterior (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x₀ : d → ℝ) (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) : DiscreteLaw ((S → ℕ) × (S → Ω)) :=
  varyingBlockPrior (fun k : S => posteriorLabelLaw H Q θ hθ hθ1 x₀ r x k.val) (fun _ => kernel)

theorem designPosterior_weight (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x₀ : d → ℝ) (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) (z : (S → ℕ) × (S → Ω)) :
    (designPosterior H kernel Q S θ hθ hθ1 x₀ r x).weight z =
      ∏ k : S, H.weight (z.1 k) * sitesCarrierFactor Q θ x₀ r x k.val (z.1 k) /
        H.expect (sitesCarrierFactor Q θ x₀ r x k.val) * (kernel (z.1 k)).weight (z.2 k) := by
  rw [designPosterior, varyingBlockPrior_weight]
  rfl

theorem designPosterior_expect (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x₀ : d → ℝ) (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ)
    (L : ((S → ℕ) × (S → Ω)) → ℝ) :
    (designPosterior H kernel Q S θ hθ hθ1 x₀ r x).expect L =
      ((blockPrior (K := S) H kernel).expect
        (fun z => ∏ i, unnormalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)))⁻¹ *
        (blockPrior H kernel).expect (fun z =>
          (∏ i, unnormalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) * L z) := by
  have he := blockPrior_tilt_product H kernel
    (fun k : S => sitesCarrierFactor Q θ x₀ r x k.val)
    (fun _ : S => (1 - θ) ^ n) (fun _ : S => (1 + θ) ^ n)
    (fun _ => pow_pos (sub_pos.mpr hθ1) n)
    (fun k => sitesCarrierFactor_bounds Q θ hθ hθ1 x₀ r x k.val)
  have hp : designPosterior H kernel Q S θ hθ hθ1 x₀ r x = _ := he.symm
  rw [hp, DiscreteLaw.tilt_expect]
  simp only [design_sample_factorization]

theorem designPosterior_Bayes (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x₀ : d → ℝ) (r : ℝ) (n : ℕ) (x : Fin n → d → ℝ)
    (L : ((S → ℕ) × (S → Ω)) → ℝ) :
    (tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r n).expect
      (fun z => (∏ i, normalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) * L z) /
      (tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r n).expect
        (fun z => ∏ i, normalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) =
      (designPosterior H kernel Q S θ hθ hθ1 x₀ r x).expect L := by
  have hden := tiltedBlockPrior_cancellation Q S θ hθ hθ1 H kernel x₀ r n x (fun _ => 1)
  simp only [mul_one] at hden
  rw [tiltedBlockPrior_cancellation, hden, designPosterior_expect]
  have hz : 0 < (blockPrior (K := S) H kernel).expect (fun z => blockNormalizer Q S θ x₀ r z.1 ^ n) :=
    (pow_pos (pow_pos (sub_pos.mpr hθ1) _) _).trans_le
      ((blockPrior (K := S) H kernel).expect_bounds _ _ _
        (pow_nonneg (pow_nonneg (sub_nonneg.mpr hθ1.le) _) _)
        (fun z => blockNormalizerPow_bounds Q S θ hθ hθ1 x₀ r n z.1)).1
  rw [mul_div_mul_left _ _ (inv_ne_zero hz.ne')]
  ring

end CausalLowerbound.PartB.ShellGeometry

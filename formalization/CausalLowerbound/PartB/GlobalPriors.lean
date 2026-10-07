import CausalLowerbound.PartB.PhysicalDesign
import CausalLowerbound.PartB.NuisanceLegality
import CausalLowerbound.DiscreteTilt

/-! Actual finite-block, countably supported priors and their Z^n tilt. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
open MeasureTheory
namespace CausalLowerbound.PartB.ShellGeometry
variable {d Ω K : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

def extendLabels (S : Finset (d → ℤ)) (H : S → ℕ) (k : d → ℤ) : ℕ :=
  if hk : k ∈ S then H ⟨k, hk⟩ else 0

def blockKernel [Fintype K] [DecidableEq K] (kernel : ℕ → FiniteLaw Ω) (H : K → ℕ) : FiniteLaw (K → Ω) :=
  FiniteLaw.independent (fun k => kernel (H k))

def blockPrior [Fintype K] [DecidableEq K] (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω) :
    DiscreteLaw ((K → ℕ) × (K → Ω)) :=
  (DiscreteLaw.independent (fun _ : K => H)).joint (blockKernel kernel)

/-- This is exactly the independent product of the local joint laws. -/
theorem blockPrior_weight [Fintype K] [DecidableEq K] (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw Ω) (z : (K → ℕ) × (K → Ω)) :
    (blockPrior H kernel).weight z = ∏ k, (H.joint kernel).weight (z.1 k, z.2 k) := by
  change (DiscreteLaw.independent (fun _ : K => H)).weight z.1 *
    (FiniteLaw.independent (fun k => kernel (z.1 k))).weight z.2 = _
  rw [DiscreteLaw.independent_weight]
  simp only [FiniteLaw.independent, DiscreteLaw.joint, Finset.prod_mul_distrib]

def blockNormalizer (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (x₀ : d → ℝ) (r : ℝ) (H : S → ℕ) : ℝ :=
  designNormalizer Q S θ (extendLabels S H) x₀ r

theorem blockNormalizerPow_bounds (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) (H : S → ℕ) :
    ((1 - θ) ^ (5 ^ Fintype.card d)) ^ n ≤ blockNormalizer Q S θ x₀ r H ^ n ∧
      blockNormalizer Q S θ x₀ r H ^ n ≤ ((1 + θ) ^ (5 ^ Fintype.card d)) ^ n := by
  have hb := designNormalizer_bounds Q S θ hθ hθ1 (extendLabels S H) x₀ r
  have hl := pow_nonneg (sub_nonneg.mpr hθ1.le) (5 ^ Fintype.card d)
  exact ⟨pow_le_pow_left₀ hl hb.1 n, pow_le_pow_left₀ (hl.trans hb.1) hb.2 n⟩

def tiltedBlockPrior (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) :
    DiscreteLaw ((S → ℕ) × (S → Ω)) :=
  (blockPrior H kernel).tilt
    (fun z => blockNormalizer Q S θ x₀ r z.1 ^ n)
    (((1 - θ) ^ (5 ^ Fintype.card d)) ^ n) (((1 + θ) ^ (5 ^ Fintype.card d)) ^ n)
    (pow_pos (pow_pos (sub_pos.mpr hθ1) _) _)
    (fun z => blockNormalizerPow_bounds Q S θ hθ hθ1 x₀ r n z.1)

theorem tiltedBlockPrior_common_label [MeasurableSpace Ω]
    (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (H : DiscreteLaw ℕ) (P Qk : ℕ → FiniteLaw Ω) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) :
    (tiltedBlockPrior Q S θ hθ hθ1 H P x₀ r n).toMeasure.map Prod.fst =
      (tiltedBlockPrior Q S θ hθ hθ1 H Qk x₀ r n).toMeasure.map Prod.fst := by
  unfold tiltedBlockPrior blockPrior
  rw [DiscreteLaw.tilt_joint (w := fun z => blockNormalizer Q S θ x₀ r z ^ n)
      (hw := blockNormalizerPow_bounds Q S θ hθ hθ1 x₀ r n),
    DiscreteLaw.tilt_joint (w := fun z => blockNormalizer Q S θ x₀ r z ^ n)
      (hw := blockNormalizerPow_bounds Q S θ hθ hθ1 x₀ r n),
    DiscreteLaw.joint_measure_label, DiscreteLaw.joint_measure_label]

theorem tiltedBlockPrior_cancellation (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (x₀ : d → ℝ) (r : ℝ) (n : ℕ) (x : Fin n → d → ℝ)
    (L : ((S → ℕ) × (S → Ω)) → ℝ) :
    (tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r n).expect
      (fun z => (∏ i, normalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) * L z) =
      ((blockPrior (K := S) H kernel).expect (fun z => blockNormalizer Q S θ x₀ r z.1 ^ n))⁻¹ *
        (blockPrior H kernel).expect
          (fun z => (∏ i, unnormalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) * L z) := by
  exact DiscreteLaw.tilt_likelihood_cancellation (blockPrior (K := S) H kernel)
    (fun z => blockNormalizer Q S θ x₀ r z.1) n
    ((1 - θ) ^ (5 ^ Fintype.card d)) ((1 + θ) ^ (5 ^ Fintype.card d))
    (pow_pos (sub_pos.mpr hθ1) _) (fun z => designNormalizer_bounds Q S θ hθ hθ1 _ _ _)
    (fun z i => unnormalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) L

theorem tiltedBlockPrior_common_design_density (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ) (P Qk : ℕ → FiniteLaw Ω)
    (x₀ : d → ℝ) (r : ℝ) (n : ℕ) (x : Fin n → d → ℝ) :
    (tiltedBlockPrior Q S θ hθ hθ1 H P x₀ r n).expect
      (fun z => ∏ i, normalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) =
    (tiltedBlockPrior Q S θ hθ hθ1 H Qk x₀ r n).expect
      (fun z => ∏ i, normalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) := by
  have hprod (hlabels : S → ℕ) :
      |∏ i, normalizedDesign Q S θ (extendLabels S hlabels) x₀ r (x i)| ≤
        ((1 + θ) ^ (5 ^ Fintype.card d) / (1 - θ) ^ (5 ^ Fintype.card d)) ^ n := by
    rw [Finset.abs_prod]
    have hlo : 0 ≤ (1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d) := by
      apply div_nonneg (pow_nonneg (sub_nonneg.mpr hθ1.le) _) (by positivity)
    calc
      _ ≤ ∏ _i : Fin n, ((1 + θ) ^ (5 ^ Fintype.card d) / (1 - θ) ^ (5 ^ Fintype.card d)) := by
        apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        intro i _
        have hx := (normalizedDesign_legal Q S θ hθ hθ1 (extendLabels S hlabels) x₀ r).2.2 (x i)
        rw [abs_of_nonneg (hlo.trans hx.1)]
        exact hx.2
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold tiltedBlockPrior blockPrior
  rw [DiscreteLaw.tilt_joint (w := fun z => blockNormalizer Q S θ x₀ r z ^ n)
      (hw := blockNormalizerPow_bounds Q S θ hθ hθ1 x₀ r n),
    DiscreteLaw.tilt_joint (w := fun z => blockNormalizer Q S θ x₀ r z ^ n)
      (hw := blockNormalizerPow_bounds Q S θ hθ hθ1 x₀ r n)]
  rw [DiscreteLaw.joint_expect_label _ _ _ _ hprod, DiscreteLaw.joint_expect_label _ _ _ _ hprod]

end CausalLowerbound.PartB.ShellGeometry

import CausalLowerbound.PartB.GlobalPriors

/-! The normalized design as a probability measure; the two tilted priors
give exactly the same continuous n-sample design marginal. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators ENNReal Classical
open MeasureTheory
namespace CausalLowerbound.PartB.ShellGeometry
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

def designMeasure (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (H : (d → ℤ) → ℕ) (x₀ : d → ℝ) (r : ℝ) : Measure (d → ℝ) :=
  (cubeMeasure d).withDensity (fun x => ENNReal.ofReal (normalizedDesign Q S θ H x₀ r x))

theorem designMeasure_probability (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : (d → ℤ) → ℕ) (x₀ : d → ℝ) (r : ℝ) :
    IsProbabilityMeasure (designMeasure Q S θ H x₀ r) := by
  have hl := normalizedDesign_legal Q S θ hθ hθ1 H x₀ r
  have hi : Integrable (normalizedDesign Q S θ H x₀ r) (cubeMeasure d) :=
    (design_integrable Q S θ hθ hθ1 H x₀ r).div_const _
  have hn : ∀ x, 0 ≤ normalizedDesign Q S θ H x₀ r x := by
    intro x
    exact (div_nonneg (pow_nonneg (sub_nonneg.mpr hθ1.le) _) (by positivity)).trans (hl.2.2 x).1
  constructor
  rw [designMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn), hl.2.1, ENNReal.ofReal_one]

def designSampleMeasure (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (H : S → ℕ) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) : Measure (Fin n → d → ℝ) :=
  Measure.pi (fun _ : Fin n => designMeasure Q S θ (extendLabels S H) x₀ r)

theorem designSampleMeasure_probability (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : S → ℕ) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) :
    IsProbabilityMeasure (designSampleMeasure Q S θ H x₀ r n) := by
  letI := designMeasure_probability Q S θ hθ hθ1 (extendLabels S H) x₀ r
  exact inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => designMeasure Q S θ (extendLabels S H) x₀ r)))

def mixedDesignExperiment (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) :
    Measure (Fin n → d → ℝ) :=
  (tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r n).mixMeasures
    (fun z => designSampleMeasure Q S θ z.1 x₀ r n)

theorem mixedDesignExperiment_probability (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (x₀ : d → ℝ) (r : ℝ) (n : ℕ) :
    IsProbabilityMeasure (mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n) := by
  letI (z : (S → ℕ) × (S → Ω)) := designSampleMeasure_probability Q S θ hθ hθ1 z.1 x₀ r n
  exact DiscreteLaw.mixMeasures_probability _ _

theorem tiltedBlockPrior_common_Xn (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ) (P Qk : ℕ → FiniteLaw Ω)
    (x₀ : d → ℝ) (r : ℝ) (n : ℕ) :
    mixedDesignExperiment Q S θ hθ hθ1 H P x₀ r n =
      mixedDesignExperiment Q S θ hθ hθ1 H Qk x₀ r n := by
  exact DiscreteLaw.tilted_common_mixture
    (DiscreteLaw.independent (fun _ : S => H)) (blockKernel P) (blockKernel Qk)
    (fun z => blockNormalizer Q S θ x₀ r z ^ n)
    (((1 - θ) ^ (5 ^ Fintype.card d)) ^ n) (((1 + θ) ^ (5 ^ Fintype.card d)) ^ n)
    (pow_pos (pow_pos (sub_pos.mpr hθ1) _) _)
    (blockNormalizerPow_bounds Q S θ hθ hθ1 x₀ r n)
    (fun z => designSampleMeasure Q S θ z x₀ r n)

theorem tiltedBlockPrior_common_density_law [MeasurableSpace Ω]
    (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (H : DiscreteLaw ℕ) (P Qk : ℕ → FiniteLaw Ω) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) :
    (tiltedBlockPrior Q S θ hθ hθ1 H P x₀ r n).toMeasure.map
      (fun z => normalizedDesign Q S θ (extendLabels S z.1) x₀ r) =
    (tiltedBlockPrior Q S θ hθ hθ1 H Qk x₀ r n).toMeasure.map
      (fun z => normalizedDesign Q S θ (extendLabels S z.1) x₀ r) := by
  let g : (S → ℕ) → (d → ℝ) → ℝ := fun z => normalizedDesign Q S θ (extendLabels S z) x₀ r
  have hg : Measurable g := measurable_of_countable _
  change Measure.map (g ∘ Prod.fst) _ = Measure.map (g ∘ Prod.fst) _
  rw [← Measure.map_map hg measurable_fst, ← Measure.map_map hg measurable_fst,
    tiltedBlockPrior_common_label Q S θ hθ hθ1 H P Qk x₀ r n]

end CausalLowerbound.PartB.ShellGeometry

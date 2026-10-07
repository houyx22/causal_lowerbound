import CausalLowerbound.PartB.DesignExperiments
import CausalLowerbound.FiniteProductMeasures

/-! Actual coordinate marginals of the tilted, mixed design experiment.
The domination constant depends on the number of retained coordinates,
not on the total sample size or on the chosen positive carrier kernel. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal NNReal Classical
namespace CausalLowerbound.PartB.ShellGeometry
variable {d Ω I : Type*} [Fintype d] [DecidableEq d] [Fintype Ω] [Fintype I]

def designDensityCeiling (d : Type*) [Fintype d] (θ : ℝ) : ℝ≥0 :=
  ((1 + θ) ^ (5 ^ Fintype.card d) / (1 - θ) ^ (5 ^ Fintype.card d)).toNNReal

theorem designMeasure_le (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : (d → ℤ) → ℕ) (x₀ : d → ℝ) (r : ℝ) :
    designMeasure Q S θ H x₀ r ≤ designDensityCeiling d θ • cubeMeasure d := by
  change (cubeMeasure d).withDensity _ ≤ (designDensityCeiling d θ : ℝ≥0∞) • cubeMeasure d
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [] with x
  exact ENNReal.ofReal_le_ofReal ((normalizedDesign_legal Q S θ hθ hθ1 H x₀ r).2.2 x).2

theorem designSample_coordinate_map (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : S → ℕ) (x₀ : d → ℝ) (r : ℝ)
    (n : ℕ) (e : I → Fin n) (he : Function.Injective e) :
    (designSampleMeasure Q S θ H x₀ r n).map (fun x i => x (e i)) =
      Measure.pi (fun _ : I => designMeasure Q S θ (extendLabels S H) x₀ r) := by
  letI := designMeasure_probability Q S θ hθ hθ1 (extendLabels S H) x₀ r
  exact (measurePreserving_coordinateSelection _ e he).map_eq

theorem mixedDesign_coordinate_le (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (x₀ : d → ℝ) (r : ℝ) (n : ℕ) (e : I → Fin n) (he : Function.Injective e) :
    (mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n).map (fun x i => x (e i)) ≤
      (designDensityCeiling d θ ^ Fintype.card I) • Measure.pi (fun _ : I => cubeMeasure d) := by
  rw [mixedDesignExperiment, DiscreteLaw.mixMeasures_map _ _ _
    (measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i)))]
  apply DiscreteLaw.mixMeasures_le
  intro z
  rw [designSample_coordinate_map Q S θ hθ hθ1 z.1 x₀ r n e he]
  exact finiteProduct_le_smul _ _ _ (fun _ => designMeasure_le Q S θ hθ hθ1 _ x₀ r)

theorem mixedDesign_coordinate_volume_le (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (x₀ : d → ℝ) (r : ℝ) (n : ℕ) (e : I → Fin n) (he : Function.Injective e) :
    (mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n).map (fun x i => x (e i)) ≤
      (designDensityCeiling d θ ^ Fintype.card I) • (volume : Measure (I → d → ℝ)) := by
  apply (mixedDesign_coordinate_le Q S θ hθ hθ1 H kernel x₀ r n e he).trans
  have hh : Measure.pi (fun _ : I => cubeMeasure d) ≤ (volume : Measure (I → d → ℝ)) :=
    finiteProduct_mono _ _ (fun _ => Measure.restrict_le_self)
  apply Measure.le_iff.mpr
  intro A _
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  exact mul_le_mul_left' (hh A) _

theorem mixedDesign_cylinder_le (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (x₀ : d → ℝ) (r : ℝ) (n : ℕ) (e : I → Fin n) (he : Function.Injective e)
    (A : Set (I → d → ℝ)) (hA : MeasurableSet A) :
    mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n
        ((fun x i => x (e i)) ⁻¹' A) ≤
      (designDensityCeiling d θ : ℝ≥0∞) ^ Fintype.card I * volume A := by
  have hb := mixedDesign_coordinate_volume_le Q S θ hθ hθ1 H kernel x₀ r n e he A
  rwa [Measure.map_apply (measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i))) hA,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow] at hb

theorem mixedDesign_coordinate_integrable (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (x₀ : d → ℝ) (r : ℝ) (n : ℕ) (e : I → Fin n) (he : Function.Injective e)
    (F : (I → d → ℝ) → ℝ) (hFi : Integrable F volume) :
    Integrable (fun x => F (fun i => x (e i)))
      (mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n) := by
  have hm : Measurable (fun x : Fin n → d → ℝ => fun i => x (e i)) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i))
  exact ((hFi.smul_measure_nnreal (c := designDensityCeiling d θ ^ Fintype.card I)).mono_measure
    (mixedDesign_coordinate_volume_le Q S θ hθ hθ1 H kernel x₀ r n e he)).comp_measurable hm

theorem mixedDesign_coordinate_integral_le (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (x₀ : d → ℝ) (r : ℝ) (n : ℕ) (e : I → Fin n) (he : Function.Injective e)
    (F : (I → d → ℝ) → ℝ) (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hFi : Integrable F volume) :
    (∫ x, F (fun i => x (e i)) ∂mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n) ≤
      (designDensityCeiling d θ : ℝ) ^ Fintype.card I * ∫ x, F x := by
  let μ := mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n
  have hm : Measurable (fun x : Fin n → d → ℝ => fun i => x (e i)) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i))
  rw [← integral_map hm.aemeasurable hFm.aestronglyMeasurable]
  have hh := integral_mono_measure (mixedDesign_coordinate_volume_le Q S θ hθ hθ1 H kernel x₀ r n e he)
    (ae_of_all _ hF0) (hFi.smul_measure (c := (designDensityCeiling d θ ^ Fintype.card I : ℝ≥0∞)) (by simp))
  simpa only [ENNReal.smul_def, integral_smul_measure, ENNReal.coe_toReal,
    NNReal.coe_pow, smul_eq_mul] using hh

end CausalLowerbound.PartB.ShellGeometry

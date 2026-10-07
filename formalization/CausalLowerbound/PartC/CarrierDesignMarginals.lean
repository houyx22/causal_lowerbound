import CausalLowerbound.PartC.GlobalPriors
import CausalLowerbound.PartB.DesignMarginals

/-! Finite-coordinate domination for the actual tilted mixed design.
Conditionally iid design laws have a uniform one-point ceiling, and any
probability mixture preserves the resulting bound. Constants depend on
the retained coordinate count, not on the full sample size. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal NNReal Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {d K J Ω I : Type*} [Fintype d] [DecidableEq d]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype Ω] [Fintype I] {θ : ℝ}

theorem CarrierProfile.measure_le (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) :
    F.measure S x₀ r ≤ designDensityCeiling d θ • cubeMeasure d := by
  change (cubeMeasure d).withDensity _ ≤ (designDensityCeiling d θ : ℝ≥0∞) • cubeMeasure d
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [] with x
  exact ENNReal.ofReal_le_ofReal ((F.normalized_legal hθ hθ1 S x₀ r).2.2 x).2

theorem CarrierProfile.sampleMeasure_coordinate_map (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) (e : I → Fin n) (he : Function.Injective e) :
    (F.sampleMeasure S x₀ r n).map (fun x i => x (e i)) =
      Measure.pi (fun _ : I => F.measure S x₀ r) := by
  letI := F.measure_probability hθ hθ1 S x₀ r
  exact (measurePreserving_coordinateSelection _ e he).map_eq

theorem mixedCarrierDesign_coordinate_le
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) (e : I → Fin n) (he : Function.Injective e) :
    (mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n).map (fun x i => x (e i)) ≤
      (designDensityCeiling d θ ^ Fintype.card I) • Measure.pi (fun _ : I => cubeMeasure d) := by
  rw [mixedCarrierDesign, DiscreteLaw.mixMeasures_map _ _ _
    (measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i)))]
  apply DiscreteLaw.mixMeasures_le
  intro z
  rw [(F z.1).sampleMeasure_coordinate_map hθ hθ1 S x₀ r n e he]
  exact finiteProduct_le_smul _ _ _ (fun _ => (F z.1).measure_le hθ hθ1 S x₀ r)

theorem mixedCarrierDesign_coordinate_volume_le
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) (e : I → Fin n) (he : Function.Injective e) :
    (mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n).map (fun x i => x (e i)) ≤
      (designDensityCeiling d θ ^ Fintype.card I) • (volume : Measure (I → d → ℝ)) := by
  apply (mixedCarrierDesign_coordinate_le F hθ hθ1 S x₀ r H kernel n e he).trans
  have hh : Measure.pi (fun _ : I => cubeMeasure d) ≤ (volume : Measure (I → d → ℝ)) :=
    finiteProduct_mono _ _ (fun _ => Measure.restrict_le_self)
  apply Measure.le_iff.mpr
  intro A _
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  exact mul_le_mul_left' (hh A) _

theorem mixedCarrierDesign_cylinder_le
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) (e : I → Fin n) (he : Function.Injective e)
    (A : Set (I → d → ℝ)) (hA : MeasurableSet A) :
    mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n ((fun x i => x (e i)) ⁻¹' A) ≤
      (designDensityCeiling d θ : ℝ≥0∞) ^ Fintype.card I * volume A := by
  have hb := mixedCarrierDesign_coordinate_volume_le F hθ hθ1 S x₀ r H kernel n e he A
  rwa [Measure.map_apply (measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i))) hA,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow] at hb

theorem mixedCarrierDesign_coordinate_integrable
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) (e : I → Fin n) (he : Function.Injective e)
    (f : (I → d → ℝ) → ℝ) (hfi : Integrable f volume) :
    Integrable (fun x => f (fun i => x (e i))) (mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) := by
  have hm : Measurable (fun x : Fin n → d → ℝ => fun i => x (e i)) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i))
  exact ((hfi.smul_measure_nnreal (c := designDensityCeiling d θ ^ Fintype.card I)).mono_measure
    (mixedCarrierDesign_coordinate_volume_le F hθ hθ1 S x₀ r H kernel n e he)).comp_measurable hm

theorem mixedCarrierDesign_coordinate_integral_le
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) (e : I → Fin n) (he : Function.Injective e)
    (f : (I → d → ℝ) → ℝ) (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f volume) :
    (∫ x, f (fun i => x (e i)) ∂mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) ≤
      (designDensityCeiling d θ : ℝ) ^ Fintype.card I * ∫ x, f x := by
  have hm : Measurable (fun x : Fin n → d → ℝ => fun i => x (e i)) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i))
  rw [← integral_map hm.aemeasurable hfm.aestronglyMeasurable]
  have hh := integral_mono_measure
    (mixedCarrierDesign_coordinate_volume_le F hθ hθ1 S x₀ r H kernel n e he)
    (ae_of_all _ hf0) (hfi.smul_measure (c := (designDensityCeiling d θ ^ Fintype.card I : ℝ≥0∞)) (by simp))
  simpa only [ENNReal.smul_def, integral_smul_measure, ENNReal.coe_toReal,
    NNReal.coe_pow, smul_eq_mul] using hh

end CausalLowerbound.PartC

import CausalLowerbound.PartC.DensityCarrierPosterior
import Mathlib.MeasureTheory.Integral.Prod

/-! Integrated ghost defects for an actual bounded density family.
The bound charges the full bad-set volume, while retaining the true
design density throughout both integrations. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
variable {X I G : Type*} [Fintype I] [Fintype G]

def completedCarrierDensity (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ)
    (v : (I → X) × (G → X)) : ℝ := carrierMarginal H density (Sum.elim v.1 v.2)

def carrierGhostDefect [MeasurableSpace X] (μ : Measure X) (H : DiscreteLaw ℕ)
    (density : ℕ → X → ℝ) (χ : (I → X) × (G → X) → ℝ) (u : I → X) : ℝ :=
  ∫ z : G → X, completedCarrierDensity H density (u, z) * (1 - χ (u, z))
    ∂Measure.pi (fun _ : G => μ)

theorem completedCarrierDensity_continuous [TopologicalSpace X]
    (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ) (B : ℝ) (_hB : 0 ≤ B)
    (hc : ∀ n, Continuous (density n)) (hb : ∀ n x, |density n x| ≤ B) :
    Continuous (completedCarrierDensity (I := I) (G := G) H density) := by
  have hd : Continuous (carrierMarginal (I := I ⊕ G) H density) := by
    exact H.expect_continuous (fun n (u : I ⊕ G → X) => carrierTensor density n u)
      (B ^ Fintype.card (I ⊕ G)) (fun n => carrierTensor_continuous density hc n)
      (fun n u => carrierTensor_abs_le density B hb n u)
  apply hd.comp
  apply continuous_pi
  intro i
  cases i with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr i => exact (continuous_apply i).comp continuous_snd

theorem completedCarrierDensity_bounds (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ)
    (lower upper : ℝ) (hlo : 0 ≤ lower)
    (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper) (v : (I → X) × (G → X)) :
    lower ^ Fintype.card (I ⊕ G) ≤ completedCarrierDensity H density v ∧
      completedCarrierDensity H density v ≤ upper ^ Fintype.card (I ⊕ G) :=
  carrierMarginal_bounds H density lower upper hlo hb (Sum.elim v.1 v.2)

theorem carrierGhostDefect_nonneg [MeasurableSpace X] (μ : Measure X) (H : DiscreteLaw ℕ)
    (density : ℕ → X → ℝ) (lower upper : ℝ) (hlo : 0 ≤ lower)
    (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper)
    (χ : (I → X) × (G → X) → ℝ) (hχ : ∀ x, χ x ≤ 1) (u : I → X) :
    0 ≤ carrierGhostDefect μ H density χ u :=
  integral_nonneg (fun z => mul_nonneg
    ((pow_nonneg hlo _).trans (completedCarrierDensity_bounds H density lower upper hlo hb (u, z)).1)
    (sub_nonneg.mpr (hχ (u, z))))

variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

theorem carrierGhostDefect_le_marginal (μ : Measure X) [IsProbabilityMeasure μ]
    (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ) (lower upper : ℝ) (hlo : 0 ≤ lower) (hup : 0 ≤ upper)
    (hc : ∀ n, Continuous (density n)) (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper)
    (hint : ∀ n, (∫ x, density n x ∂μ) = 1)
    (χ : (I → X) × (G → X) → ℝ) (hχc : Continuous χ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (u : I → X) :
    carrierGhostDefect μ H density χ u ≤ carrierMarginal H density u := by
  let ν := Measure.pi (fun _ : G => μ)
  let f := fun z : G → X => completedCarrierDensity H density (u, z)
  have hab (n : ℕ) (x : X) : |density n x| ≤ upper := by
    rw [abs_of_nonneg (hlo.trans (hb n x).1)]
    exact (hb n x).2
  have hf : Continuous f := (completedCarrierDensity_continuous H density upper hup hc hab).comp
    ((continuous_const : Continuous (fun _ : G → X => u)).prodMk continuous_id)
  have hg := hχc.comp ((continuous_const : Continuous (fun _ : G → X => u)).prodMk continuous_id)
  have hfb (z : G → X) : 0 ≤ f z ∧ f z ≤ upper ^ Fintype.card (I ⊕ G) := by
    have hh := completedCarrierDensity_bounds H density lower upper hlo hb (u, z)
    exact ⟨(pow_nonneg hlo _).trans hh.1, hh.2⟩
  have hi : Integrable f ν := (integrable_const (upper ^ Fintype.card (I ⊕ G))).mono'
    hf.aestronglyMeasurable (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hfb z).1]; exact (hfb z).2))
  have hij : Integrable (fun z => f z * (1 - χ (u, z))) ν := by
    apply (integrable_const (upper ^ Fintype.card (I ⊕ G))).mono'
      ((hf.mul (continuous_const.sub hg)).aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro z
    change ‖f z * (1 - χ (u, z))‖ ≤ upper ^ Fintype.card (I ⊕ G)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hfb z).1 (sub_nonneg.mpr (hχ (u, z)).2))]
    exact (mul_le_of_le_one_right (hfb z).1 (by linarith [(hχ (u, z)).1])).trans (hfb z).2
  have hp := weightedCarrierMarginal_projective (G := G) μ H density (fun _ => 1) upper 1 hup hc hab hint (by simp) u
  have hproj : (∫ z, f z ∂ν) = carrierMarginal H density u := by
    simpa only [weightedCarrierMarginal, carrierMarginal, mul_one] using hp
  calc
    _ ≤ ∫ z, f z ∂ν := integral_mono hij hi (fun z =>
      mul_le_of_le_one_right (hfb z).1 (by linarith [(hχ (u, z)).1]))
    _ = _ := hproj

theorem completedCarrierDefect_integrable (ν : Measure ((I → X) × (G → X))) [IsFiniteMeasure ν]
    (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ) (lower upper : ℝ) (hlo : 0 ≤ lower) (hup : 0 ≤ upper)
    (hc : ∀ n, Continuous (density n)) (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper)
    (χ : (I → X) × (G → X) → ℝ) (hχc : Continuous χ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    Integrable (fun v => completedCarrierDensity H density v * (1 - χ v)) ν := by
  have hab (n : ℕ) (x : X) : |density n x| ≤ upper := by
    rw [abs_of_nonneg (hlo.trans (hb n x).1)]
    exact (hb n x).2
  have hdc := completedCarrierDensity_continuous (I := I) (G := G) H density upper hup hc hab
  apply (integrable_const (upper ^ Fintype.card (I ⊕ G))).mono'
    ((hdc.mul (continuous_const.sub hχc)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro v
  have hd := completedCarrierDensity_bounds H density lower upper hlo hb v
  have hd0 : 0 ≤ completedCarrierDensity H density v := (pow_nonneg hlo _).trans hd.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hd0 (sub_nonneg.mpr (hχ v).2))]
  exact (mul_le_of_le_one_right hd0 (by linarith [(hχ v).1])).trans hd.2

theorem carrierGhostDefect_integrable (μ : Measure X) [IsProbabilityMeasure μ]
    (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ) (lower upper : ℝ) (hlo : 0 ≤ lower) (hup : 0 ≤ upper)
    (hc : ∀ n, Continuous (density n)) (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper)
    (χ : (I → X) × (G → X) → ℝ) (hχc : Continuous χ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    Integrable (carrierGhostDefect μ H density χ) (Measure.pi (fun _ : I => μ)) :=
  (completedCarrierDefect_integrable
    ((Measure.pi (fun _ : I => μ)).prod (Measure.pi (fun _ : G => μ)))
    H density lower upper hlo hup hc hb χ hχc hχ).integral_prod_left

theorem integrated_carrierGhostDefect (μ : Measure X) [IsProbabilityMeasure μ]
    (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ) (lower upper : ℝ) (hlo : 0 ≤ lower) (hup : 0 ≤ upper)
    (hc : ∀ n, Continuous (density n)) (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper)
    (χ : (I → X) × (G → X) → ℝ) (hχc : Continuous χ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    (∫ u : I → X, carrierGhostDefect μ H density χ u ∂Measure.pi (fun _ : I => μ)) =
      ∫ v : (I → X) × (G → X), completedCarrierDensity H density v * (1 - χ v)
        ∂(Measure.pi (fun _ : I => μ)).prod (Measure.pi (fun _ : G => μ)) := by
  exact (integral_prod _ (completedCarrierDefect_integrable _ H density lower upper hlo hup hc hb χ hχc hχ)).symm

theorem carrierGhostDefect_volume_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (H : DiscreteLaw ℕ) (density : ℕ → X → ℝ) (lower upper : ℝ) (hlo : 0 ≤ lower) (hup : 0 ≤ upper)
    (hc : ∀ n, Continuous (density n)) (hb : ∀ n x, lower ≤ density n x ∧ density n x ≤ upper)
    (χ : (I → X) × (G → X) → ℝ) (hχc : Continuous χ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    (∫ u : I → X, carrierGhostDefect μ H density χ u ∂Measure.pi (fun _ : I => μ)) ≤
      upper ^ Fintype.card (I ⊕ G) *
        ((Measure.pi (fun _ : I => μ)).prod (Measure.pi (fun _ : G => μ))).real {v | χ v ≠ 1} := by
  rw [integrated_carrierGhostDefect μ H density lower upper hlo hup hc hb χ hχc hχ]
  let ν := (Measure.pi (fun _ : I => μ)).prod (Measure.pi (fun _ : G => μ))
  let bad := {v : (I → X) × (G → X) | χ v ≠ 1}
  have hbad : MeasurableSet bad := (isClosed_singleton.preimage hχc).measurableSet.compl
  have hi := completedCarrierDefect_integrable ν H density lower upper hlo hup hc hb χ hχc hχ
  calc
    _ ≤ ∫ v, bad.indicator (fun _ => upper ^ Fintype.card (I ⊕ G)) v ∂ν := by
      apply integral_mono hi ((integrable_const _).indicator hbad)
      intro v
      by_cases hv : v ∈ bad
      · rw [Set.indicator_of_mem hv]
        have hd := completedCarrierDensity_bounds H density lower upper hlo hb v
        have hd0 : 0 ≤ completedCarrierDensity H density v := (pow_nonneg hlo _).trans hd.1
        exact (mul_le_of_le_one_right hd0 (by linarith [(hχ v).1])).trans hd.2
      · have he : χ v = 1 := by simpa only [bad, Set.mem_setOf_eq, not_not] using hv
        simp [Set.indicator_of_not_mem hv, he]
    _ = _ := by rw [integral_indicator hbad]; simp [mul_comm, bad, ν, measureReal_def]

end CausalLowerbound.PartC

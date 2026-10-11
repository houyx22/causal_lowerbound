import CausalLowerbound.PartB.HighComponentProbability
import CausalLowerbound.PartB.ComponentSize

/-! Uniform-design cluster and close-pair bounds. Constants for a fixed
cluster cutoff do not depend on the sample size or bandwidths. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.UniformLowerBound
open PartB PartB.ShellGeometry
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I]

def uniformDesign (d : Type*) [Fintype d] (n : ℕ) : Measure (Fin n → d → ℝ) :=
  Measure.pi (fun _ : Fin n => cubeMeasure d)

instance uniformDesign_probability (n : ℕ) : IsProbabilityMeasure (uniformDesign d n) := by
  unfold uniformDesign
  infer_instance

theorem uniformDesign_coordinate_map (n : ℕ) (e : I → Fin n) (he : Function.Injective e) :
    (uniformDesign d n).map (fun x i => x (e i)) =
      Measure.pi (fun _ : I => cubeMeasure d) :=
  (measurePreserving_coordinateSelection (cubeMeasure d) e he).map_eq

theorem uniformDesign_coordinate_volume_le (n : ℕ) (e : I → Fin n)
    (he : Function.Injective e) :
    (uniformDesign d n).map (fun x i => x (e i)) ≤ (volume : Measure (I → d → ℝ)) := by
  rw [uniformDesign_coordinate_map n e he]
  exact finiteProduct_mono _ _ (fun _ => Measure.restrict_le_self)

theorem uniformDesign_cylinder_le (n : ℕ) (e : I → Fin n) (he : Function.Injective e)
    (A : Set (I → d → ℝ)) (hA : MeasurableSet A) :
    uniformDesign d n ((fun x i => x (e i)) ⁻¹' A) ≤ volume A := by
  have hb := uniformDesign_coordinate_volume_le (d := d) n e he A
  rwa [Measure.map_apply (measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i))) hA] at hb

theorem uniformDesign_coordinate_integrable (n : ℕ) (e : I → Fin n)
    (he : Function.Injective e) (F : (I → d → ℝ) → ℝ) (hF : Integrable F volume) :
    Integrable (fun x => F (fun i => x (e i))) (uniformDesign d n) := by
  exact (hF.mono_measure (uniformDesign_coordinate_volume_le n e he)).comp_measurable
    (measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i)))

theorem uniformDesign_coordinate_integral_le (n : ℕ) (e : I → Fin n)
    (he : Function.Injective e) (F : (I → d → ℝ) → ℝ)
    (hFm : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hFi : Integrable F volume) :
    (∫ x, F (fun i => x (e i)) ∂uniformDesign d n) ≤ ∫ x, F x := by
  rw [← integral_map (measurable_pi_iff.mpr
    (fun i => measurable_pi_apply (e i))).aemeasurable hFm.aestronglyMeasurable]
  exact integral_mono_measure (uniformDesign_coordinate_volume_le n e he)
    (ae_of_all _ hF0) hFi

theorem embedding_card_le (n q : ℕ) : Fintype.card (Fin q ↪ Fin n) ≤ n ^ q := by
  have hh := Fintype.card_le_of_injective
    (fun e : Fin q ↪ Fin n => (e : Fin q → Fin n))
    (fun e f hef => Function.Embedding.ext (congrFun hef))
  simpa using hh

theorem uniformDesign_largeCluster_probability_le (n Q : ℕ)
    (x₀ : d → ℝ) (ℓ h : ℝ) :
    uniformDesign d n (largeClusterEvent n Q x₀ ℓ h) ≤
      (n : ℝ≥0∞) ^ (Q + 1) *
        (ENNReal.ofReal (2 * ((5 + 4 * Q) * h)) ^ Fintype.card d *
          ENNReal.ofReal (2 * (8 * ℓ * Q)) ^ (Q * Fintype.card d)) := by
  let A := labelledCluster Q x₀ ((5 + 4 * Q) * h) (8 * ℓ * Q)
  have hb (e : Fin (Q + 1) ↪ Fin n) :
      uniformDesign d n ((fun x i => x (e i)) ⁻¹' A) ≤ volume A :=
    uniformDesign_cylinder_le n e e.injective A (labelledCluster_measurable Q x₀ _ _)
  calc
    _ ≤ ∑ e : Fin (Q + 1) ↪ Fin n,
        uniformDesign d n ((fun x i => x (e i)) ⁻¹' A) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _e : Fin (Q + 1) ↪ Fin n, volume A := Finset.sum_le_sum (fun e _ => hb e)
    _ = Fintype.card (Fin (Q + 1) ↪ Fin n) * volume A := by simp
    _ ≤ (n : ℝ≥0∞) ^ (Q + 1) * volume A :=
      mul_le_mul_right' (by exact_mod_cast embedding_card_le n (Q + 1)) _
    _ = _ := by simp only [A, labelledCluster_volume]

def clusterConstant (d : Type*) [Fintype d] (Q : ℕ) : ℝ :=
  (2 * (5 + 4 * Q)) ^ Fintype.card d * (16 * Q) ^ (Q * Fintype.card d)

theorem clusterConstant_nonneg (Q : ℕ) : 0 ≤ clusterConstant d Q := by
  unfold clusterConstant
  positivity

theorem uniformDesign_largeCluster_real_probability_le (n Q : ℕ)
    (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 ≤ ℓ) (hh : 0 ≤ h) :
    (uniformDesign d n).real (largeClusterEvent n Q x₀ ℓ h) ≤
      clusterConstant d Q * ((n : ℝ) ^ (Q + 1) * h ^ Fintype.card d *
        ℓ ^ (Q * Fintype.card d)) := by
  have hb := ENNReal.toReal_mono (by
    apply ENNReal.mul_ne_top
    · exact ENNReal.pow_ne_top (by simp)
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    (uniformDesign_largeCluster_probability_le n Q x₀ ℓ h)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ((5 + 4 * Q) * h)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (8 * ℓ * Q))] at hb
  convert hb using 1
  unfold clusterConstant
  rw [show 2 * ((5 + 4 * (Q : ℝ)) * h) = (2 * (5 + 4 * Q)) * h by ring,
    show 2 * (8 * ℓ * (Q : ℝ)) = (16 * Q) * ℓ by ring]
  simp only [mul_pow]
  ring

def collisionCount (x₀ : d → ℝ) (ℓ h : ℝ) {n : ℕ} (x : Fin n → d → ℝ) : ℝ :=
  ∑ e : Fin 2 ↪ Fin n, (labelledCluster 1 x₀ (5 * h) (4 * ℓ)).indicator
    (fun _ => (1 : ℝ)) (fun i => x (e i))

theorem collisionCount_nonneg (x₀ : d → ℝ) (ℓ h : ℝ) {n : ℕ} (x : Fin n → d → ℝ) :
    0 ≤ collisionCount x₀ ℓ h x :=
  Finset.sum_nonneg (fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem collisionCount_measurable (x₀ : d → ℝ) (ℓ h : ℝ) (n : ℕ) :
    Measurable (fun x : Fin n → d → ℝ => collisionCount x₀ ℓ h x) := by
  apply Finset.measurable_sum
  intro e _
  exact (measurable_const.indicator (labelledCluster_measurable 1 x₀ (5 * h) (4 * ℓ))).comp
    (measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i)))

theorem collision_indicator_integrable (x₀ : d → ℝ) (ℓ h : ℝ) :
    Integrable ((labelledCluster 1 x₀ (5 * h) (4 * ℓ)).indicator (fun _ => (1 : ℝ))) volume := by
  apply (integrable_indicator_iff (labelledCluster_measurable 1 x₀ (5 * h) (4 * ℓ))).mpr
  apply integrableOn_const.mpr (Or.inr _)
  rw [labelledCluster_volume]
  exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))

theorem collisionCount_integrable (x₀ : d → ℝ) (ℓ h : ℝ) (n : ℕ) :
    Integrable (fun x : Fin n → d → ℝ => collisionCount x₀ ℓ h x) (uniformDesign d n) :=
  integrable_finset_sum _ (fun e _ => uniformDesign_coordinate_integrable n e e.injective _
    (collision_indicator_integrable x₀ ℓ h))

theorem collisionCount_integral_le (x₀ : d → ℝ) (ℓ h : ℝ)
    (hℓ : 0 ≤ ℓ) (hh : 0 ≤ h) (n : ℕ) :
    (∫ x, collisionCount x₀ ℓ h x ∂uniformDesign d n) ≤
      (n : ℝ) ^ 2 * ((10 * h) ^ Fintype.card d * (8 * ℓ) ^ Fintype.card d) := by
  let A := labelledCluster 1 x₀ (5 * h) (4 * ℓ)
  have hA : MeasurableSet A := labelledCluster_measurable 1 x₀ (5 * h) (4 * ℓ)
  have hvol : volume.real A = (10 * h) ^ Fintype.card d * (8 * ℓ) ^ Fintype.card d := by
    simp only [Measure.real, A, labelledCluster_volume, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (5 * h)),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (4 * ℓ)), one_mul]
    congr 2 <;> ring
  have hb (e : Fin 2 ↪ Fin n) :
      (∫ x, A.indicator (fun _ => (1 : ℝ)) (fun i => x (e i)) ∂uniformDesign d n) ≤
        (10 * h) ^ Fintype.card d * (8 * ℓ) ^ Fintype.card d := by
    have hb := uniformDesign_coordinate_integral_le n e e.injective
      (A.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hA)
      (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x) (collision_indicator_integrable x₀ ℓ h)
    simpa only [integral_indicator_const (1 : ℝ) hA, smul_eq_mul, mul_one, hvol] using hb
  unfold collisionCount
  rw [integral_finset_sum _ (fun (e : Fin 2 ↪ Fin n) _ =>
    uniformDesign_coordinate_integrable n e e.injective _ (collision_indicator_integrable x₀ ℓ h))]
  calc
    _ ≤ ∑ _e : Fin 2 ↪ Fin n, (10 * h) ^ Fintype.card d * (8 * ℓ) ^ Fintype.card d :=
      Finset.sum_le_sum (fun e _ => hb e)
    _ = (Fintype.card (Fin 2 ↪ Fin n) : ℝ) *
        ((10 * h) ^ Fintype.card d * (8 * ℓ) ^ Fintype.card d) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast embedding_card_le n 2) (by positivity)

end CausalLowerbound.UniformLowerBound

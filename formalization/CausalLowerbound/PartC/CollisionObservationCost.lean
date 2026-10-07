import CausalLowerbound.PartC.CarrierDesignMarginals
import CausalLowerbound.PartC.SharedCarrierGeometry
import CausalLowerbound.PartB.ClusterVolume

/-! A measurable count of ordered close pairs in the coarse region.
The actual two-coordinate design marginal gives an expectation of order
n^2 h^d ℓ^d, without a density factor depending on the full sample size. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt incidenceComponentFintype
variable {d K J Ω : Type*} [Fintype d] [DecidableEq d]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype Ω] {θ : ℝ}

def collisionObservationCost (x₀ : d → ℝ) (ℓ h : ℝ) {n : ℕ} (x : Fin n → d → ℝ) : ℝ :=
  ∑ e : Fin 2 ↪ Fin n, (labelledCluster 1 x₀ (5 * h) (2 * ℓ)).indicator
    (fun _ => (1 : ℝ)) (fun i => x (e i))

theorem collisionObservationCost_nonneg (x₀ : d → ℝ) (ℓ h : ℝ) {n : ℕ} (x : Fin n → d → ℝ) :
    0 ≤ collisionObservationCost x₀ ℓ h x :=
  Finset.sum_nonneg (fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem collisionObservationCost_measurable (x₀ : d → ℝ) (ℓ h : ℝ) (n : ℕ) :
    Measurable (fun x : Fin n → d → ℝ => collisionObservationCost x₀ ℓ h x) := by
  apply Finset.measurable_sum
  intro e _
  exact (measurable_const.indicator (labelledCluster_measurable 1 x₀ (5 * h) (2 * ℓ))).comp
    (measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i)))

theorem collision_label_indicator_integrable (x₀ : d → ℝ) (ℓ h : ℝ) :
    Integrable ((labelledCluster 1 x₀ (5 * h) (2 * ℓ)).indicator (fun _ => (1 : ℝ))) volume := by
  apply (integrable_indicator_iff (labelledCluster_measurable 1 x₀ (5 * h) (2 * ℓ))).mpr
  apply integrableOn_const.mpr (Or.inr _)
  rw [labelledCluster_volume]
  exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))

theorem mixedCarrierDesign_collisionObservationCost_integrable
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) :
    Integrable (fun x : Fin n → d → ℝ => collisionObservationCost x₀ ℓ h x)
      (mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) := by
  exact integrable_finset_sum _ (fun e _ => mixedCarrierDesign_coordinate_integrable F hθ hθ1
    S x₀ r H kernel n e e.injective _ (collision_label_indicator_integrable x₀ ℓ h))

theorem mixedCarrierDesign_collisionObservationCost_integral_le
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h : ℝ) (hℓ : 0 ≤ ℓ) (hh : 0 ≤ h)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) :
    (∫ x, collisionObservationCost x₀ ℓ h x ∂mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) ≤
      (n : ℝ) ^ 2 * (designDensityCeiling d θ : ℝ) ^ 2 *
        ((10 * h) ^ Fintype.card d * (4 * ℓ) ^ Fintype.card d) := by
  let A := labelledCluster 1 x₀ (5 * h) (2 * ℓ)
  have hA : MeasurableSet A := labelledCluster_measurable 1 x₀ (5 * h) (2 * ℓ)
  have hvol : volume.real A = (10 * h) ^ Fintype.card d * (4 * ℓ) ^ Fintype.card d := by
    simp only [Measure.real, A, labelledCluster_volume, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (5 * h)),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (2 * ℓ)), one_mul]
    congr 2 <;> ring
  have hb (e : Fin 2 ↪ Fin n) :
      (∫ x, A.indicator (fun _ => (1 : ℝ)) (fun i => x (e i))
        ∂mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) ≤
        (designDensityCeiling d θ : ℝ) ^ 2 * ((10 * h) ^ Fintype.card d * (4 * ℓ) ^ Fintype.card d) := by
    have hb := mixedCarrierDesign_coordinate_integral_le F hθ hθ1 S x₀ r H kernel n e e.injective
      (A.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hA)
      (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x) (collision_label_indicator_integrable x₀ ℓ h)
    simpa only [Fintype.card_fin, integral_indicator_const (1 : ℝ) hA,
      smul_eq_mul, mul_one, hvol] using hb
  have hcard : Fintype.card (Fin 2 ↪ Fin n) ≤ n ^ 2 := by
    have hh := Fintype.card_le_of_injective
      (fun e : Fin 2 ↪ Fin n => (e : Fin 2 → Fin n))
      (fun e f hef => Function.Embedding.ext (congrFun hef))
    simpa using hh
  unfold collisionObservationCost
  rw [integral_finset_sum _ (fun (e : Fin 2 ↪ Fin n) _ => mixedCarrierDesign_coordinate_integrable F hθ hθ1
    S x₀ r H kernel n e e.injective _ (collision_label_indicator_integrable x₀ ℓ h))]
  calc
    _ ≤ ∑ _e : Fin 2 ↪ Fin n, (designDensityCeiling d θ : ℝ) ^ 2 *
        ((10 * h) ^ Fintype.card d * (4 * ℓ) ^ Fintype.card d) := Finset.sum_le_sum (fun e _ => hb e)
    _ = (Fintype.card (Fin 2 ↪ Fin n) : ℝ) * ((designDensityCeiling d θ : ℝ) ^ 2 *
        ((10 * h) ^ Fintype.card d * (4 * ℓ) ^ Fintype.card d)) := by simp
    _ ≤ (n : ℝ) ^ 2 * ((designDensityCeiling d θ : ℝ) ^ 2 *
        ((10 * h) ^ Fintype.card d * (4 * ℓ) ^ Fintype.card d)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring

end CausalLowerbound.PartC

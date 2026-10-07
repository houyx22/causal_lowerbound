import CausalLowerbound.PartC.CarrierDesign
import CausalLowerbound.FiniteProductDensities

/-! Densities of the actual iid covariates conditional on one carrier
profile. These pointwise bounds are uniform in labels and shared signs. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.PartC.CarrierProfile
open PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d] {θ : ℝ}

def sampleDensity (F : CarrierProfile d θ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) : ℝ := ∏ i, F.normalized S x₀ r (x i)

theorem sampleDensity_measurable (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) :
    Measurable (F.sampleDensity S x₀ r (n := n)) :=
  Finset.measurable_prod _ (fun i _ =>
    (F.normalized_legal hθ hθ1 S x₀ r).1.comp (measurable_pi_apply i))

theorem sampleDensity_bounds (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) :
    ((1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d)) ^ n ≤ F.sampleDensity S x₀ r x ∧
      F.sampleDensity S x₀ r x ≤ ((1 + θ) ^ (5 ^ Fintype.card d) / (1 - θ) ^ (5 ^ Fintype.card d)) ^ n := by
  have hl : 0 ≤ (1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d) :=
    div_nonneg (pow_nonneg (sub_nonneg.mpr hθ1.le) _) (by positivity)
  have hb := (F.normalized_legal hθ hθ1 S x₀ r).2.2
  constructor
  · simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin n =>
        (1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d))
        (fun _ _ => hl) (fun i _ => (hb (x i)).1))
  · simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod (s := Finset.univ) (f := fun i : Fin n => F.normalized S x₀ r (x i))
        (fun i _ => hl.trans (hb (x i)).1) (fun i _ => (hb (x i)).2))

theorem sampleDensity_pos (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) :
    0 < F.sampleDensity S x₀ r x :=
  (pow_pos (div_pos (pow_pos (sub_pos.mpr hθ1) _) (pow_pos (by linarith) _)) n).trans_le
    (F.sampleDensity_bounds hθ hθ1 S x₀ r x).1

theorem sampleMeasure_density (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) :
    F.sampleMeasure S x₀ r n = (Measure.pi (fun _ : Fin n => cubeMeasure d)).withDensity
      (fun x => ENNReal.ofReal (F.sampleDensity S x₀ r x)) := by
  letI := F.measure_probability hθ hθ1 S x₀ r
  exact finiteProduct_withDensity (fun _ : Fin n => cubeMeasure d)
    (fun _ => F.normalized S x₀ r)
    (fun _ => (F.product_integrable hθ hθ1 S x₀ r).div_const _)
    (fun _ => F.normalized_nonneg hθ hθ1 S x₀ r)

end CausalLowerbound.PartC.CarrierProfile

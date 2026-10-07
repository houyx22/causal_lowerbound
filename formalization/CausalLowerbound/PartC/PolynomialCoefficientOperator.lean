import CausalLowerbound.PartC.RepresentativeRealExpansion
import CausalLowerbound.PartC.VectorSeries

/-! The complete bounded linear polarization operator. Its output is an
actual absolutely summable family of Walsh coefficient arrays. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.PartC.Representative

open PartB.Polarization

abbrev PolarizationCoefficients (d ι J : Type*) (D : ℕ) :=
  VectorSeries.Family (PolynomialAtom d ι D) (Walsh.Coefficients J)

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

def polynomialStencil (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J) (θ : ℝ)
    (v : PolynomialBasis d ι D × Finset J) : PolarizationCoefficients d ι J D :=
  ∑ m : Masks ι, lp.single 1 (v.1, m)
    (Walsh.product (lp.single 1 v.2 1) (Walsh.polarizationWeight (center v.1) (θ / 2) m))

theorem polynomialStencil_bound (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (v : PolynomialBasis d ι D × Finset J) :
    ‖polynomialStencil center θ v‖ ≤ stencilBound (ι := ι) (θ / 2) := by
  calc
    _ ≤ ∑ m : Masks ι, ‖(lp.single 1 (v.1, m)
        (Walsh.product (lp.single 1 v.2 1) (Walsh.polarizationWeight (center v.1) (θ / 2) m)) :
          PolarizationCoefficients d ι J D)‖ := norm_sum_le _ _
    _ ≤ ∑ m : Masks ι, ‖Walsh.polarizationWeight (center v.1) (θ / 2) m‖ := by
      apply Finset.sum_le_sum
      intro m _
      rw [lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))]
      simpa only [lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞)), norm_one, one_mul] using
        Walsh.product_norm (lp.single 1 v.2 1) (Walsh.polarizationWeight (center v.1) (θ / 2) m)
    _ ≤ _ := Walsh.polarizationWeight_bound (center v.1) (hc v.1) (θ / 2)

def polynomialCoefficientOperator (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) :
    RealExpansion d ι J D →L[ℝ] PolarizationCoefficients d ι J D :=
  Wiener.synthesis (polynomialStencil center θ) (stencilBound (ι := ι) (θ / 2))
    (polynomialStencil_bound center hc θ)

theorem polynomialCoefficientOperator_single (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (v : PolynomialBasis d ι D × Finset J) (t : ℝ) :
    polynomialCoefficientOperator center hc θ (lp.single 1 v t) = t • polynomialStencil center θ v :=
  Wiener.synthesis_single _ _ _ v t

theorem polynomialCoefficientOperator_bound (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (a : RealExpansion d ι J D) :
    ‖polynomialCoefficientOperator center hc θ a‖ ≤ stencilBound (ι := ι) (θ / 2) * ‖a‖ :=
  Wiener.norm_synthesis (polynomialStencil center θ) (stencilBound (ι := ι) (θ / 2))
    (polynomialStencil_bound center hc θ) a

def polarizationOperator (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) : Array d ι J D →L[ℝ] PolarizationCoefficients d ι J D :=
  (polynomialCoefficientOperator center hc θ).comp canonicalRealExpansion

def polarizationBound (ι : Type*) [Fintype ι] [DecidableEq ι] (θ : ℝ) : ℝ :=
  stencilBound (ι := ι) (θ / 2) * (2 : ℝ) ^ Fintype.card ι

theorem polarizationOperator_bound (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (a : Array d ι J D) :
    ‖polarizationOperator center hc θ a‖ ≤ polarizationBound ι θ * ‖a‖ := by
  have hC : 0 ≤ stencilBound (ι := ι) (θ / 2) :=
    mul_nonneg (pow_nonneg (by positivity) _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hp := polynomialCoefficientOperator_bound center hc θ (canonicalRealExpansion a)
  have he := mul_le_mul_of_nonneg_left (canonicalRealExpansion_bound a) hC
  rw [polarizationOperator, ContinuousLinearMap.comp_apply, polarizationBound, mul_assoc]
  exact hp.trans he

theorem polarizationOperator_summable (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (a : Array d ι J D) :
    Summable (fun m => ‖polarizationOperator center hc θ a m‖) :=
  (VectorSeries.hasSum_norm _).summable

theorem polarizationOperator_lipschitz (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (a b : Array d ι J D) :
    (∑' m, ‖polarizationOperator center hc θ a m - polarizationOperator center hc θ b m‖) ≤
      polarizationBound ι θ * ‖a - b‖ := by
  have h := polarizationOperator_bound center hc θ (a - b)
  rw [map_sub, VectorSeries.norm_eq_tsum] at h
  exact h

end CausalLowerbound.PartC.Representative

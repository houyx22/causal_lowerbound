import CausalLowerbound.PartC.PolynomialCoefficientOperator
import CausalLowerbound.PartC.RepresentativeRealReconstruction

/-! Reconstruction by the complete Walsh-valued polarization operator.
All infinite sums converge absolutely, with bounds independent of the
number of rough signs. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.PartC.Representative

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

def polynomialLabelEvaluation (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (θ : ℝ) (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool)
    (m : PolynomialAtom d ι D) : Walsh.Coefficients J →L[ℝ] ℝ :=
  (Walsh.evaluate ζ).smulRight (pointValue x z ζ (polynomialAtomTensor m.1 (center m.1) θ m.2))

@[simp] theorem polynomialLabelEvaluation_apply
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (θ : ℝ) (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool)
    (m : PolynomialAtom d ι D) (a : Walsh.Coefficients J) :
    polynomialLabelEvaluation center θ x z ζ m a =
      Walsh.evaluate ζ a * pointValue x z ζ (polynomialAtomTensor m.1 (center m.1) θ m.2) := rfl

theorem polynomialLabelEvaluation_bound
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (x : Wiener.Torus (ι × d))
    (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool)
    (m : PolynomialAtom d ι D) (a : Walsh.Coefficients J) :
    ‖polynomialLabelEvaluation center θ x z ζ m a‖ ≤ (1 + |θ|) ^ Fintype.card ι * ‖a‖ := by
  rw [polynomialLabelEvaluation_apply, Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul ((pointValue_bound x z hz ζ _).trans
    (polynomialAtomTensor_norm m.1 (center m.1) (hc m.1) θ m.2))
    (Walsh.evaluate_bound ζ a) (abs_nonneg _) (by positivity)

def polynomialDensitySynthesis
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (x : Wiener.Torus (ι × d))
    (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool) :
    PolarizationCoefficients d ι J D →L[ℝ] ℝ :=
  VectorSeries.synthesis (polynomialLabelEvaluation center θ x z ζ)
    ((1 + |θ|) ^ Fintype.card ι) (polynomialLabelEvaluation_bound center hc θ x z hz ζ)

theorem polynomialDensitySynthesis_single
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (x : Wiener.Torus (ι × d))
    (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool)
    (m : PolynomialAtom d ι D) (a : Walsh.Coefficients J) :
    polynomialDensitySynthesis center hc θ x z hz ζ (lp.single 1 m a) =
      Walsh.evaluate ζ a * pointValue x z ζ (polynomialAtomTensor m.1 (center m.1) θ m.2) :=
  VectorSeries.synthesis_single _ _ _ m a

theorem polynomialStencil_evaluation [Nonempty ι]
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (hθ : θ ≠ 0)
    (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool)
    (v : PolynomialBasis d ι D × Finset J) :
    polynomialDensitySynthesis center hc θ x z hz ζ (polynomialStencil center θ v) =
      Walsh.character v.2 ζ * pointValue x z ζ (polynomialBasisTensor v.1 : Array d ι J D) := by
  simp only [polynomialStencil, map_sum, polynomialDensitySynthesis_single,
    Walsh.evaluate_product, Walsh.evaluate_single, one_mul]
  rw [polynomial_basis_polarization v.1 (center v.1) θ hθ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem polynomialCoefficientOperator_evaluation [Nonempty ι]
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (hθ : θ ≠ 0)
    (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool)
    (a : RealExpansion d ι J D) :
    polynomialDensitySynthesis center hc θ x z hz ζ (polynomialCoefficientOperator center hc θ a) =
      expansionPointEvaluation x z hz ζ a := by
  have he : (polynomialDensitySynthesis center hc θ x z hz ζ).comp
      (polynomialCoefficientOperator center hc θ) = expansionPointEvaluation x z hz ζ := by
    apply lp.ext_continuousLinearMap (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    intro v
    apply ContinuousLinearMap.ext
    intro c
    change polynomialDensitySynthesis center hc θ x z hz ζ
      (polynomialCoefficientOperator center hc θ (lp.single 1 v c)) =
        expansionPointEvaluation x z hz ζ (lp.single 1 v c)
    rw [polynomialCoefficientOperator_single, map_smul, polynomialStencil_evaluation center hc θ hθ]
    exact (expansionPointEvaluation_single x z hz ζ v.1 v.2 c).symm
  exact congrArg (fun f : RealExpansion d ι J D →L[ℝ] ℝ => f a) he

theorem polarizationOperator_hasSum [Nonempty ι]
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (hθ : θ ≠ 0)
    (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool)
    (a : Array d ι J D) :
    HasSum (fun m : PolynomialAtom d ι D => Walsh.evaluate ζ (polarizationOperator center hc θ a m) *
      pointValue x z ζ (polynomialAtomTensor m.1 (center m.1) θ m.2))
        (symmetricPointEvaluation x z hz ζ a) := by
  have hs := VectorSeries.synthesis_hasSum (polynomialLabelEvaluation center θ x z ζ)
    ((1 + |θ|) ^ Fintype.card ι) (polynomialLabelEvaluation_bound center hc θ x z hz ζ)
      (polarizationOperator center hc θ a)
  change HasSum _ (polynomialDensitySynthesis center hc θ x z hz ζ
    (polynomialCoefficientOperator center hc θ (canonicalRealExpansion a))) at hs
  rw [polynomialCoefficientOperator_evaluation center hc θ hθ, canonicalRealExpansion_value] at hs
  exact hs

theorem polarizationOperator_reconstruction [Nonempty ι]
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (hθ : θ ≠ 0)
    (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool)
    (a : Array d ι J D)
    (hsym : ∀ σ : Equiv.Perm ι,
      pointValue (Wiener.permuteSlots σ.symm x) (fun i => z (σ.symm i)) ζ a = pointValue x z ζ a) :
    HasSum (fun m : PolynomialAtom d ι D => Walsh.evaluate ζ (polarizationOperator center hc θ a m) *
      pointValue x z ζ (polynomialAtomTensor m.1 (center m.1) θ m.2)) (pointValue x z ζ a) := by
  have hs := polarizationOperator_hasSum center hc θ hθ x z hz ζ a
  rw [← canonicalRealExpansion_value, canonicalRealExpansion_reconstruction a x z hz ζ hsym] at hs
  exact hs

end CausalLowerbound.PartC.Representative

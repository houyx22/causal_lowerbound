import CausalLowerbound.PartC.PolynomialSeriesReconstruction

/-! The positive polarization series converges in the uniform norm on
every compact chart. This supplies the function-space reconstruction
needed by the common-label carrier theorem. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.PartC.Representative

variable {d ι J K : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ} [TopologicalSpace K] [CompactSpace K]

def polynomialChartLabel (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (θ : ℝ) (x : K → Wiener.Torus (ι × d)) (hx : Continuous x)
    (z : ι → K → ℝ) (hz : ∀ i, Continuous (z i)) (hb : ∀ i u, |z i u| ≤ 1)
    (ζ : J → Bool) (m : PolynomialAtom d ι D) : Walsh.Coefficients J →L[ℝ] C(K, ℝ) :=
  (Walsh.evaluate ζ).smulRight
    (chartEvaluation x hx z hz hb ζ (polynomialAtomTensor m.1 (center m.1) θ m.2))

theorem polynomialChartLabel_bound
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ)
    (x : K → Wiener.Torus (ι × d)) (hx : Continuous x)
    (z : ι → K → ℝ) (hz : ∀ i, Continuous (z i)) (hb : ∀ i u, |z i u| ≤ 1)
    (ζ : J → Bool) (m : PolynomialAtom d ι D) (a : Walsh.Coefficients J) :
    ‖polynomialChartLabel center θ x hx z hz hb ζ m a‖ ≤ (1 + |θ|) ^ Fintype.card ι * ‖a‖ := by
  rw [polynomialChartLabel, ContinuousLinearMap.smulRight_apply, norm_smul, mul_comm]
  exact mul_le_mul ((chartEvaluation_bound x hx z hz hb ζ _).trans
    (polynomialAtomTensor_norm m.1 (center m.1) (hc m.1) θ m.2))
    (Walsh.evaluate_bound ζ a) (norm_nonneg _) (by positivity)

def polynomialChartSynthesis
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ)
    (x : K → Wiener.Torus (ι × d)) (hx : Continuous x)
    (z : ι → K → ℝ) (hz : ∀ i, Continuous (z i)) (hb : ∀ i u, |z i u| ≤ 1)
    (ζ : J → Bool) : PolarizationCoefficients d ι J D →L[ℝ] C(K, ℝ) :=
  VectorSeries.synthesis (polynomialChartLabel center θ x hx z hz hb ζ)
    ((1 + |θ|) ^ Fintype.card ι) (polynomialChartLabel_bound center hc θ x hx z hz hb ζ)

theorem polarizationOperator_chart_reconstruction [Nonempty ι]
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (hθ : θ ≠ 0)
    (x : K → Wiener.Torus (ι × d)) (hx : Continuous x)
    (z : ι → K → ℝ) (hz : ∀ i, Continuous (z i)) (hb : ∀ i u, |z i u| ≤ 1)
    (ζ : J → Bool) (a : Array d ι J D)
    (hsym : ∀ u (σ : Equiv.Perm ι), pointValue (Wiener.permuteSlots σ.symm (x u))
      (fun i => z (σ.symm i) u) ζ a = pointValue (x u) (fun i => z i u) ζ a) :
    polynomialChartSynthesis center hc θ x hx z hz hb ζ (polarizationOperator center hc θ a) =
      chartEvaluation x hx z hz hb ζ a := by
  have hs := VectorSeries.synthesis_hasSum (polynomialChartLabel center θ x hx z hz hb ζ)
    ((1 + |θ|) ^ Fintype.card ι) (polynomialChartLabel_bound center hc θ x hx z hz hb ζ)
      (polarizationOperator center hc θ a)
  apply ContinuousMap.ext
  intro u
  have he : HasSum (fun m : PolynomialAtom d ι D =>
      Walsh.evaluate ζ (polarizationOperator center hc θ a m) *
        pointValue (x u) (fun i => z i u) ζ (polynomialAtomTensor m.1 (center m.1) θ m.2))
      (polynomialChartSynthesis center hc θ x hx z hz hb ζ (polarizationOperator center hc θ a) u) := by
    simpa only [polynomialChartLabel, ContinuousLinearMap.smulRight_apply,
      ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul, chartEvaluation_apply] using
        (ContinuousMap.evalCLM ℝ u).hasSum hs
  exact he.unique (polarizationOperator_reconstruction center hc θ hθ
    (x u) (fun i => z i u) (fun i => hb i u) ζ a (hsym u))

theorem polarizationOperator_chart_hasSum [Nonempty ι]
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (hθ : θ ≠ 0)
    (x : K → Wiener.Torus (ι × d)) (hx : Continuous x)
    (z : ι → K → ℝ) (hz : ∀ i, Continuous (z i)) (hb : ∀ i u, |z i u| ≤ 1)
    (ζ : J → Bool) (a : Array d ι J D)
    (hsym : ∀ u (σ : Equiv.Perm ι), pointValue (Wiener.permuteSlots σ.symm (x u))
      (fun i => z (σ.symm i) u) ζ a = pointValue (x u) (fun i => z i u) ζ a) :
    HasSum (fun m : PolynomialAtom d ι D =>
      Walsh.evaluate ζ (polarizationOperator center hc θ a m) •
        chartEvaluation x hx z hz hb ζ (polynomialAtomTensor m.1 (center m.1) θ m.2))
      (chartEvaluation x hx z hz hb ζ a) := by
  have hs := VectorSeries.synthesis_hasSum (polynomialChartLabel center θ x hx z hz hb ζ)
    ((1 + |θ|) ^ Fintype.card ι) (polynomialChartLabel_bound center hc θ x hx z hz hb ζ)
      (polarizationOperator center hc θ a)
  change HasSum _ (polynomialChartSynthesis center hc θ x hx z hz hb ζ
    (polarizationOperator center hc θ a)) at hs
  rw [polarizationOperator_chart_reconstruction center hc θ hθ x hx z hz hb ζ a hsym] at hs
  exact hs

end CausalLowerbound.PartC.Representative

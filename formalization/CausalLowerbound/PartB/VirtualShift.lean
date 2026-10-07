import CausalLowerbound.PartB.LagrangeInterpolation
import CausalLowerbound.PartB.LagrangePointwise

/-! The actual coefficient vectors interpolate the independent site jitter,
and their virtual shifts remain uniformly small on the taper support. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace CausalLowerbound.PartB.ShellGeometry
open ConfigurationShells

variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [LinearOrder V]

def coefficientEvaluation {Q : ℕ} (U : CoefficientExponent d Q → ℝ) (x : d → ℝ) : ℝ :=
  ∑ b, U b * polynomialFeature x b

def virtualCoefficientShift {Q : ℕ} (U : CoefficientExponent d Q → ℝ)
    (u : V × d → ℝ) (t : ℝ) (ζ : V → ℝ) : CoefficientExponent d Q → ℝ :=
  fun b => U b + t * ∑ i, lagrangeCoefficient edgeLeft edgeRight i (polynomialBasisDegree b) u * ζ i

theorem virtualCoefficientShift_evaluation (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (U : CoefficientExponent d Q → ℝ) (u : V × d → ℝ)
    (hu : ∀ i j, i ≠ j → chordDistance (configurationSite u i) (configurationSite u j) ≠ 0)
    (t : ℝ) (ζ : V → ℝ) (j : V) :
    coefficientEvaluation (virtualCoefficientShift U u t ζ) (configurationSite u j) =
      coefficientEvaluation U (configurationSite u j) + t * ζ j := by
  simp only [coefficientEvaluation, virtualCoefficientShift, add_mul, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum]
  congr 1
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (i : V) : (∑ b : CoefficientExponent d Q,
      lagrangeCoefficient edgeLeft edgeRight i (polynomialBasisDegree b) u * ζ i *
        polynomialFeature (configurationSite u j) b) = (if i = j then 1 else 0) * ζ i := by
    rw [← lagrangeCoefficient_interpolates Q hQ hcard u hu i j, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [he]
  simp

theorem virtualCoefficientShift_norm_bound {Q : ℕ} (U : CoefficientExponent d Q → ℝ)
    (u : V × d → ℝ) (t ε : ℝ) (ht : 0 ≤ t) (hε : 0 < ε) (ζ : V → ℝ)
    (hζ : ∀ i, |ζ i| ≤ 1)
    (hχ : graphTaper edgeLeft edgeRight taperCutoff ε (graphDistance edgeLeft edgeRight u) ≠ 0) :
    ‖virtualCoefficientShift U u t ζ - U‖ ≤
      (Fintype.card V : ℝ) * lagrangePointwiseConstant V d * (t / ε) := by
  have hC := (lagrangePointwiseConstant_pos (V := V) (d := d)).le
  have hcb (i : V) (b : CoefficientExponent d Q) :
      |lagrangeCoefficient edgeLeft edgeRight i (polynomialBasisDegree b) u| ≤
        lagrangePointwiseConstant V d / ε := by
    have hPi := taper_nonzero_vertexProduct edgeLeft edgeRight taperCutoff
      (fun _ _ h => taperCutoff_zero h) ε hε (graphDistance edgeLeft edgeRight u)
      (fun _ => (truncatedDistance_range _ _).1) hχ i
    rw [vertexProduct_complete] at hPi
    exact (lagrangeCoefficient_abs_le i _ u (hε.trans hPi)).trans
      (div_le_div_of_nonneg_left hC hε hPi.le)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro b
  change |U b + t * (∑ i, lagrangeCoefficient edgeLeft edgeRight i (polynomialBasisDegree b) u * ζ i) - U b| ≤ _
  rw [add_sub_cancel_left, abs_mul, abs_of_nonneg ht]
  calc
    _ ≤ t * ∑ i, |lagrangeCoefficient edgeLeft edgeRight i (polynomialBasisDegree b) u * ζ i| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) ht
    _ ≤ t * ∑ _i : V, lagrangePointwiseConstant V d / ε := by
      apply mul_le_mul_of_nonneg_left _ ht
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact (mul_le_mul (hcb i b) (hζ i) (abs_nonneg _) (div_nonneg hC hε.le)).trans_eq (mul_one _)
    _ = _ := by simp [div_eq_mul_inv]; ring

/-- Uniform in the sites, signs, and baseline coefficient vector. -/
theorem virtualCoefficientShift_eventually_small (Q : ℕ) (p B ρ : ℝ) (hB : 0 < B) (hρ : 0 < ρ) :
    ∀ᶠ n : ℕ in atTop, ∀ (U : CoefficientExponent d Q → ℝ) (u : V × d → ℝ) (ζ : V → ℝ),
      (∀ i, |ζ i| ≤ 1) →
      graphTaper edgeLeft edgeRight taperCutoff (logarithmicThreshold p B (n + 1))
        (graphDistance edgeLeft edgeRight u) ≠ 0 →
      ‖virtualCoefficientShift U u (polynomialAmplitude p (n + 1)) ζ - U‖ < ρ := by
  let C : ℝ := (Fintype.card V : ℝ) * lagrangePointwiseConstant V d
  have hx : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have hl := (((tendsto_rpow_neg_atTop hB).comp logScale_tendsto).comp hx).const_mul C
  have hl' : Tendsto (fun n : ℕ => C * logScale (n + 1) ^ (-B)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using hl
  have hh : ∀ᶠ n : ℕ in atTop, C * logScale (n + 1) ^ (-B) < ρ := by
    exact hl'.eventually (gt_mem_nhds hρ)
  filter_upwards [hh] with n hn U u ζ hζ hχ
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hb := virtualCoefficientShift_norm_bound U u (polynomialAmplitude p (n + 1)) _
    (polynomialAmplitude_pos p (by positivity)).le (logarithmicThreshold_pos p B hn1) ζ hζ hχ
  rw [amplitude_threshold_ratio p B hn1] at hb
  exact hb.trans_lt hn

end CausalLowerbound.PartB.ShellGeometry

import CausalLowerbound.PartC.CubicObservationChoices
import CausalLowerbound.PartC.CubicTaylorEvaluation
import CausalLowerbound.PartC.WeightedOutcomePatterns
import CausalLowerbound.PartC.TaperedCubicFunctional

/-! Absorb the carrier normalization once per selected cubic occurrence.
The resulting shift factor is the physical amplitude, with no extra N
in the normalized pattern bounds. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative
variable {I K V d J : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]
  [Fintype d] [Fintype J] [DecidableEq J]

theorem block_cubic_observation_normalized (w : K → Degree V 3 → ℝ)
    (b : I → Fin 4 → ℝ) (δ : I → K → ℝ) (slot : K → I → V) (amp N : ℝ) :
    blockPolynomialFunctional (fun k => cubicSiteFunctional (w k))
      (∏ i, ∑ n : Fin 4, C (b i n) * (∑ k, C ((amp * N) * δ i k) * X (k, slot k i)) ^ n.val) =
      ∑ s : I → CubicObservationChoice K,
        if hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3 then
          amp ^ cubicObservationChoiceDegree s * ((∏ i, b i (s i).1) * cubicObservationChoiceWeight δ s) *
            ∏ k, N ^ degreeSize (fun v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v)) *
              w k (fun v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v))
        else 0 := by
  rw [block_cubic_observation_expansion]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3
  · rw [dif_pos hs, dif_pos hs, cubicObservationChoiceWeight_scale]
    simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      cubicObservationChoice_degree_sum slot s hs, mul_pow]
    ring
  · rw [dif_neg hs, dif_neg hs]

theorem block_outcome_taylor_normalized (κ : K → V → ℝ)
    (W : K → Array d V J 3) (u : K → V × d → ℝ) (z : K → V → ℝ) (ζ : J → Bool)
    (R T jb η smooth rough : I → ℝ) (δ : I → K → ℝ) (slot : K → I → V) (amp N : ℝ) :
    blockPolynomialFunctional (fun k => outcomePolynomialFunctional (κ k) (W k) (u k) (z k) ζ)
      (∏ i, outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i)
        (∑ k, C ((amp * N) * δ i k) * X (k, slot k i))) =
      ∑ s : I → CubicObservationChoice K,
        if hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3 then
          amp ^ cubicObservationChoiceDegree s *
            ((∏ i, outcomeTaylorCoefficient (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i) (s i).1) *
              cubicObservationChoiceWeight δ s) *
            ∏ k, weightedOutcomePatternWeight N (κ k) (W k) (u k) (z k) ζ
              (fun v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v))
        else 0 := by
  simp_rw [outcomeTaylorPolynomial_eq_sum]
  exact block_cubic_observation_normalized (fun k => outcomePatternWeight (κ k) (W k) (u k) (z k) ζ)
    (fun i => outcomeTaylorCoefficient (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i)) δ slot amp N

theorem weighted_taperedCubicWeight (χ N : ℝ) (w : Degree V 3 → ℝ) (f : Degree V 3) :
    N ^ degreeSize f * taperedCubicWeight χ w f =
      (if f = 0 then 1 else χ) * (N ^ degreeSize f * w f) := by
  by_cases hf : f = 0
  · simp only [taperedCubicWeight, if_pos hf, hf, if_true, one_mul]
  · simp only [taperedCubicWeight, if_neg hf]
    ring

end CausalLowerbound.PartC

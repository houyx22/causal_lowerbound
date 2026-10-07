import CausalLowerbound.PartC.CubicObservationFactors
import CausalLowerbound.PartC.CubicObservationNormalization
import CausalLowerbound.PartC.FinitePatternComparison

/-! Size, parity, and a finite-sum comparison for cubic patterns. These
estimates require no spatial separation or assignment-interior condition. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB Representative
variable {I K V J Ω A : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J] [Fintype Ω]

theorem cubicObservationPatternProduct_bound (w : K → Degree V 3 → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hw : ∀ k f, |w k f| ≤ M)
    (slot : K → I → V) (s : I → CubicObservationChoice K) :
    |cubicObservationPatternProduct w slot s| ≤ M ^ Fintype.card K := by
  unfold cubicObservationPatternProduct
  split
  · rw [Finset.abs_prod]
    exact (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun k _ => hw k _)).trans (by simp)
  · simpa only [abs_zero] using pow_nonneg hM (Fintype.card K)

theorem cubicObservationPatternProduct_parity
    (w : (J → Bool) → K → Degree V 3 → ℝ)
    (hw : ∀ ζ k f, w (Walsh.flip ζ) k f = (-1) ^ degreeSize f * w ζ k f)
    (slot : K → I → V) (s : I → CubicObservationChoice K) (ζ : J → Bool) :
    cubicObservationPatternProduct (w (Walsh.flip ζ)) slot s =
      (-1) ^ cubicObservationChoiceDegree s * cubicObservationPatternProduct (w ζ) slot s := by
  by_cases hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3
  · simp only [cubicObservationPatternProduct, dif_pos hs, hw, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, cubicObservationChoice_degree_sum slot s hs]
  · simp only [cubicObservationPatternProduct, dif_neg hs, mul_zero]

theorem finite_pattern_crude_comparison_bound
    (μ : FiniteLaw Ω) (choices : Finset A) (f : Ω → A → ℝ)
    (value base : Ω → ℝ) (cells : Bool → Ω → ℝ)
    (g : A → ℝ) (E C R : ℝ) (hE : 0 ≤ E)
    (hg : (∑ s ∈ choices, g s) ≤ C)
    (hf : ∀ s ∈ choices, |μ.expect (fun ω => f ω s)| ≤ g s * E)
    (hzero : ∀ ω, value ω = (∑ s ∈ choices, f ω s) + base ω * cells false ω)
    (hdelta : |μ.expect (fun ω => base ω * (cells true ω - cells false ω))| ≤ R) :
    |μ.expect value - μ.expect (fun ω => base ω * cells true ω)| ≤ C * E + R := by
  have hn : |μ.expect (fun ω => ∑ s ∈ choices, f ω s)| ≤ C * E := by
    rw [FiniteLaw.expect_finset_sum]
    calc
      _ ≤ ∑ s ∈ choices, |μ.expect (fun ω => f ω s)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ choices, g s * E := Finset.sum_le_sum hf
      _ = (∑ s ∈ choices, g s) * E := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hg hE
  have he : μ.expect value - μ.expect (fun ω => base ω * cells true ω) =
      μ.expect (fun ω => ∑ s ∈ choices, f ω s) -
        μ.expect (fun ω => base ω * (cells true ω - cells false ω)) := by
    rw [FiniteLaw.expect_congr _ hzero, FiniteLaw.expect_add]
    simp only [mul_sub, FiniteLaw.expect_sub]
    ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add hn hdelta)

end CausalLowerbound.PartC

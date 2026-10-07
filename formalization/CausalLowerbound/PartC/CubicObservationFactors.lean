import CausalLowerbound.PartC.CubicObservationBaseline

/-! Factor each complete cubic observation choice into its scalar
coefficient and its carrier pattern. Invalid site degrees contribute zero. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Representative
variable {I K V : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

def cubicObservationCoefficient (c : ℝ) (b : I → Fin 4 → ℝ)
    (δ : I → K → ℝ) (amp : ℝ) (s : I → CubicObservationChoice K) : ℝ :=
  c * amp ^ cubicObservationChoiceDegree s * (∏ i, b i (s i).1) * cubicObservationChoiceWeight δ s

def cubicObservationPatternProduct (w : K → Degree V 3 → ℝ)
    (slot : K → I → V) (s : I → CubicObservationChoice K) : ℝ :=
  if hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3 then
    ∏ k, w k (fun v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v))
  else 0

theorem cubicObservationTerm_factor (c : ℝ) (w : K → Degree V 3 → ℝ)
    (b : I → Fin 4 → ℝ) (δ : I → K → ℝ) (slot : K → I → V) (amp : ℝ)
    (s : I → CubicObservationChoice K) :
    c * cubicObservationTerm w b δ slot amp s =
      cubicObservationCoefficient c b δ amp s * cubicObservationPatternProduct w slot s := by
  unfold cubicObservationTerm cubicObservationPatternProduct cubicObservationCoefficient
  split <;> ring

theorem cubicObservationExpansion_factor (c : ℝ) (w : K → Degree V 3 → ℝ)
    (b : I → Fin 4 → ℝ) (δ : I → K → ℝ) (slot : K → I → V) (amp : ℝ) :
    c * cubicObservationExpansion w b δ slot amp =
      ∑ s, cubicObservationCoefficient c b δ amp s * cubicObservationPatternProduct w slot s := by
  change c * (∑ s, cubicObservationTerm w b δ slot amp s) = _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun s _ => cubicObservationTerm_factor c w b δ slot amp s)

theorem cubicObservationPositive_factor (c : ℝ) (w : K → Degree V 3 → ℝ)
    (b : I → Fin 4 → ℝ) (δ : I → K → ℝ) (slot : K → I → V) (amp : ℝ) :
    c * (∑ s ∈ Finset.univ.erase cubicZeroChoice, cubicObservationTerm w b δ slot amp s) =
      ∑ s ∈ Finset.univ.erase cubicZeroChoice,
        cubicObservationCoefficient c b δ amp s * cubicObservationPatternProduct w slot s := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun s _ => cubicObservationTerm_factor c w b δ slot amp s)

theorem cubicObservationExpansion_factor_baseline (c : ℝ) (w : K → Degree V 3 → ℝ)
    (b : I → Fin 4 → ℝ) (δ : I → K → ℝ) (slot : K → I → V) (amp : ℝ) :
    c * cubicObservationExpansion w b δ slot amp =
      (∑ s ∈ Finset.univ.erase cubicZeroChoice,
        cubicObservationCoefficient c b δ amp s * cubicObservationPatternProduct w slot s) +
          (∏ k, w k 0) * (c * ∏ i, b i 0) := by
  rw [cubicObservationExpansion_baseline, ← cubicObservationPositive_factor]
  ring

theorem cubicObservation_normalized_weight_sum_bound (δ : I → K → ℝ)
    (hδ : ∀ i k, |δ i k| ≤ 1) :
    (∑ s ∈ Finset.univ.erase (cubicZeroChoice : I → CubicObservationChoice K),
      (1 / 4 : ℝ) ^ Fintype.card I * |cubicObservationChoiceWeight δ s|) ≤
        (Fintype.card (I → CubicObservationChoice K) : ℝ) := by
  have hs (s : I → CubicObservationChoice K) :
      (1 / 4 : ℝ) ^ Fintype.card I * |cubicObservationChoiceWeight δ s| ≤ 1 := by
    have hw : |cubicObservationChoiceWeight δ s| ≤ 1 := by
      simpa only [one_pow] using cubicObservationChoiceWeight_bound δ 1 hδ s
    exact (mul_le_mul (pow_le_one₀ (by norm_num) (by norm_num) (n := Fintype.card I))
      hw (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  calc
    _ ≤ ∑ _s ∈ Finset.univ.erase (cubicZeroChoice : I → CubicObservationChoice K), (1 : ℝ) :=
      Finset.sum_le_sum (fun s _ => hs s)
    _ ≤ ∑ _s : I → CubicObservationChoice K, (1 : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => zero_le_one)
    _ = _ := by simp

end CausalLowerbound.PartC

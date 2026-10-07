import CausalLowerbound.PartC.CubicObservationNormalization

/-! A zero taper already annihilates every positive-degree occurrence
in its block. Consequently the auxiliary amplitude mask can be removed
from the full cubic observation polynomial before ghost integration. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative
variable {I K V : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

theorem cubicObservationChoice_degree_at_occurrence (slot : K → I → V)
    (s : I → CubicObservationChoice K)
    (hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3)
    (p : CubicObservationPositions s) :
    (fun v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs
      ((s p.1).2 p.2, v)) ≠ 0 := by
  intro hz
  have hv := congrArg Fin.val (congrFun hz (slot ((s p.1).2 p.2) p.1))
  have hp : 0 < siteOccurrenceExponent (cubicObservationChoiceSlot slot s)
      (cubicObservationChoiceSlot slot s p) := by
    rw [siteOccurrenceExponent_apply, Finset.card_pos]
    exact ⟨p, by simp⟩
  change siteOccurrenceExponent (cubicObservationChoiceSlot slot s)
    (cubicObservationChoiceSlot slot s p) = 0 at hv
  omega

theorem cubicObservationChoice_taper_mask (χ : K → ℝ) (w : K → Degree V 3 → ℝ)
    (δ : I → K → ℝ) (slot : K → I → V) (s : I → CubicObservationChoice K)
    (hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3) :
    cubicObservationChoiceWeight (fun i k => if χ k = 0 then 0 else δ i k) s *
        ∏ k, taperedCubicWeight (χ k) (w k)
          (fun v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v)) =
      cubicObservationChoiceWeight δ s *
        ∏ k, taperedCubicWeight (χ k) (w k)
          (fun v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v)) := by
  let D := fun k v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v)
  by_cases hz : (∏ k, taperedCubicWeight (χ k) (w k) (D k)) = 0
  · change cubicObservationChoiceWeight (fun i k => if χ k = 0 then 0 else δ i k) s *
      (∏ k, taperedCubicWeight (χ k) (w k) (D k)) =
        cubicObservationChoiceWeight δ s * (∏ k, taperedCubicWeight (χ k) (w k) (D k))
    simp only [hz, mul_zero]
  have hw (p : CubicObservationPositions s) : χ ((s p.1).2 p.2) ≠ 0 := by
    intro hχ
    have hk := Finset.prod_ne_zero_iff.mp hz ((s p.1).2 p.2) (Finset.mem_univ _)
    have hd : D ((s p.1).2 p.2) ≠ 0 := cubicObservationChoice_degree_at_occurrence slot s hs p
    exact hk (by simp only [taperedCubicWeight, if_neg hd, hχ, zero_mul])
  have he : cubicObservationChoiceWeight (fun i k => if χ k = 0 then 0 else δ i k) s =
      cubicObservationChoiceWeight δ s := by
    apply Finset.prod_congr rfl
    intro p _
    exact if_neg (hw p)
  rw [he]

theorem block_cubic_observation_unmask (χ : K → ℝ) (w : K → Degree V 3 → ℝ)
    (b : I → Fin 4 → ℝ) (δ : I → K → ℝ) (slot : K → I → V) :
    blockPolynomialFunctional (fun k => cubicSiteFunctional (taperedCubicWeight (χ k) (w k)))
      (∏ i, ∑ n : Fin 4, C (b i n) *
        (∑ k, C (if χ k = 0 then 0 else δ i k) * X (k, slot k i)) ^ n.val) =
      blockPolynomialFunctional (fun k => cubicSiteFunctional (taperedCubicWeight (χ k) (w k)))
        (∏ i, ∑ n : Fin 4, C (b i n) * (∑ k, C (δ i k) * X (k, slot k i)) ^ n.val) := by
  rw [block_cubic_observation_expansion, block_cubic_observation_expansion]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3
  · rw [dif_pos hs, dif_pos hs, mul_assoc, cubicObservationChoice_taper_mask χ w δ slot s hs, ← mul_assoc]
  · rw [dif_neg hs, dif_neg hs]

theorem block_outcome_taylor_unmask (χ : K → ℝ) (w : K → Degree V 3 → ℝ)
    (R T jb η smooth rough : I → ℝ) (δ : I → K → ℝ) (slot : K → I → V) :
    blockPolynomialFunctional (fun k => cubicSiteFunctional (taperedCubicWeight (χ k) (w k)))
      (∏ i, outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i)
        (∑ k, C (if χ k = 0 then 0 else δ i k) * X (k, slot k i))) =
      blockPolynomialFunctional (fun k => cubicSiteFunctional (taperedCubicWeight (χ k) (w k)))
        (∏ i, outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i)
          (∑ k, C (δ i k) * X (k, slot k i))) := by
  simp_rw [outcomeTaylorPolynomial_eq_sum]
  exact block_cubic_observation_unmask χ w
    (fun i => outcomeTaylorCoefficient (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i)) δ slot

end CausalLowerbound.PartC

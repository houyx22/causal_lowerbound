import CausalLowerbound.PartC.ObservationPatternNormalization
import CausalLowerbound.PartC.TaperedSiteFunctional

/-! Remove the amplitude mask only after multiplying by the actual taper
weights, and absorb N exactly once per selected observation. Both identities
include zero tapers, zero increments, and empty selected patterns. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB Representative
variable {d I K V J : Type*} [Fintype d] [DecidableEq d]
  [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

theorem tapered_observation_unmask (χ amp : K → ℝ) (δ : I → K → ℝ)
    (w : K → Finset V → ℝ) (slot : K → I → V) (s : I → Option K) :
    (∏ i : ShiftPositions s, δ i.val (choiceSite s i) *
      (if χ (choiceSite s i) = 0 then 0 else amp (choiceSite s i))) *
        (∏ k, taperedPatternWeight (χ k) (w k) ((observationChoiceSet s k).image (slot k))) =
    (∏ i : ShiftPositions s, δ i.val (choiceSite s i) * amp (choiceSite s i)) *
      (∏ k, taperedPatternWeight (χ k) (w k) ((observationChoiceSet s k).image (slot k))) := by
  by_cases hw : (∏ k, taperedPatternWeight (χ k) (w k)
      ((observationChoiceSet s k).image (slot k))) = 0
  · simp only [hw, mul_zero]
  apply congrArg (fun a : ℝ => a * ∏ k, taperedPatternWeight (χ k) (w k)
    ((observationChoiceSet s k).image (slot k)))
  apply Finset.prod_congr rfl
  intro i _
  have hi : i.val ∈ observationChoiceSet s (choiceSite s i) := by
    simp only [observationChoiceSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact choiceSite_some s i
  have hs : (observationChoiceSet s (choiceSite s i)).image (slot (choiceSite s i)) ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨_, Finset.mem_image.mpr ⟨i.val, hi, rfl⟩⟩
  have hχ : χ (choiceSite s i) ≠ 0 := by
    intro hz
    have hk := Finset.prod_ne_zero_iff.mp hw (choiceSite s i) (Finset.mem_univ _)
    apply hk
    simp only [taperedPatternWeight, if_neg hs, hz, zero_mul]
  rw [if_neg hχ]

theorem tapered_observation_pattern_normalization
    (amp N : ℝ) (δ : I → K → ℝ) (slot : K → I → V)
    (hslot : ∀ k i j, δ i k ≠ 0 → δ j k ≠ 0 → slot k i = slot k j → i = j)
    (χ : K → ℝ) (κ : K → V → ℝ) (W : K → Array d V J 1)
    (u : K → V × d → ℝ) (z : K → V → ℝ) (ζ : J → Bool) (s : I → Option K) :
    (∏ i : ShiftPositions s, (amp * N) * δ i.val (choiceSite s i)) *
      (∏ k, taperedPatternWeight (χ k) (propensityPatternWeight (κ k) (W k) (u k) (z k) ζ)
        ((observationChoiceSet s k).image (slot k))) =
      amp ^ choiceDegree s * (∏ i : ShiftPositions s, δ i.val (choiceSite s i)) *
        ∏ k, (if (observationChoiceSet s k).image (slot k) = ∅ then 1 else χ k) *
          weightedPropensityPatternWeight N (κ k) (W k) (u k) (z k) ζ
            ((observationChoiceSet s k).image (slot k)) := by
  let A := fun k => (observationChoiceSet s k).image (slot k)
  let f := fun k => propensityPatternWeight (κ k) (W k) (u k) (z k) ζ
  have ht (k : K) : taperedPatternWeight (χ k) (f k) (A k) =
      (if A k = ∅ then 1 else χ k) * f k (A k) := by
    by_cases hk : A k = ∅ <;> simp [taperedPatternWeight, hk]
  have hn := observation_pattern_normalization amp N δ slot hslot κ W u z ζ s
  change (∏ i : ShiftPositions s, (amp * N) * δ i.val (choiceSite s i)) * (∏ k, f k (A k)) =
    amp ^ choiceDegree s * (∏ i : ShiftPositions s, δ i.val (choiceSite s i)) *
      ∏ k, weightedPropensityPatternWeight N (κ k) (W k) (u k) (z k) ζ (A k) at hn
  change (∏ i : ShiftPositions s, (amp * N) * δ i.val (choiceSite s i)) *
    (∏ k, taperedPatternWeight (χ k) (f k) (A k)) = _
  simp_rw [ht]
  calc
    _ = ((∏ i : ShiftPositions s, (amp * N) * δ i.val (choiceSite s i)) *
      (∏ k, f k (A k))) * (∏ k, if A k = ∅ then 1 else χ k) := by
        simp only [Finset.prod_mul_distrib]
        ring
    _ = _ := by
      rw [hn]
      simp only [Finset.prod_mul_distrib]
      ring

end CausalLowerbound.PartC

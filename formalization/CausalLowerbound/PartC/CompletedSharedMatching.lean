import CausalLowerbound.PartC.RetainedPatternRows
import CausalLowerbound.PartC.ResampledCoefficientMatching
import CausalLowerbound.PartC.ObservationPatternNormalization

/-! Exact matching for completed carrier representatives with different
retained observation sets. The same resampled sign field drives every
block's Walsh coefficient and every ghost value. Nonincident selections
are eliminated by the actual zero increment, before expanding rows. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB Wiener Representative RoughPropensity
variable {d V J I K : Type*} [Fintype d] [DecidableEq d]
  [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
  [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

theorem retained_observation_rows
    (P : K → I → Prop) (G : K → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k, {i // P k i} ⊕ G k ≃ V)
    (slot : K → I → V) (hslot : ∀ k i (hi : P k i), slot k i = e k (Sum.inl ⟨i, hi⟩))
    (κ : K → V → ℝ) (scale : I → K → ℝ) (ja v X : I → ℝ)
    (hκ : ∀ k (i : {i // P k i}), κ k (e k (Sum.inl i)) =
      scale i.val k ^ 2 * ja i.val ^ 2 * v i.val ^ 2)
    (W : K → Array d V J 1) (u : K → V × d → ℝ) (η : J → Bool)
    (g : ∀ k, G k → ℝ) (a : I → ℝ) (δ : I → K → ℝ)
    (hδ : ∀ i k, δ i k ≠ 0 → P k i) :
    (∑ s : I → Option K, (choiceBase a s * ∏ i : ShiftPositions s, δ i.val (choiceSite s i)) *
      ∏ k, propensityPatternWeight (κ k) (W k) (u k)
        (completedSites (e k) (fun i => scale i.val k * X i.val) (g k)) η
        ((observationChoiceSet s k).image (slot k))) =
    ∑ s : I → Option K, (choiceBase a s * ∏ i : ShiftPositions s, δ i.val (choiceSite s i)) *
      ∏ k, ∑ r : Row V J 1, completedRowCoefficient (W k) (u k) η (e k) (g k) r *
        ∏ i, if s i = some k then normalizedSubstitution (retainedRowDegree (P k) (e k) r.1 i)
          (scale i k) (ja i) (v i) (X i)
          else (scale i k * X i) ^ retainedRowDegree (P k) (e k) r.1 i := by
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : (∏ i : ShiftPositions s, δ i.val (choiceSite s i)) = 0
  · simp only [hs, mul_zero, zero_mul]
  · apply congrArg (fun z : ℝ => (choiceBase a s * ∏ i : ShiftPositions s, δ i.val (choiceSite s i)) * z)
    apply Finset.prod_congr rfl
    intro k _
    have hA (i : I) (hi : i ∈ observationChoiceSet s k) : P k i :=
      hδ i k (observationChoiceSet_nonzero δ s hs k i hi)
    simpa only [observationChoiceSet, Finset.mem_filter, Finset.mem_univ, true_and] using
      propensityPatternWeight_retained_rows (P k) (e k) (slot k) (hslot k)
        (κ k) (fun i => scale i k) ja v X (hκ k) (W k) (u k) η (g k) (observationChoiceSet s k) hA

theorem completed_shared_pattern_matching
    (P : K → I → Prop) (G : K → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k, {i // P k i} ⊕ G k ≃ V)
    (slot : K → I → V) (hslot : ∀ k i (hi : P k i), slot k i = e k (Sum.inl ⟨i, hi⟩))
    (κ : K → V → ℝ) (W : K → Array d V J 1) (u : K → V × d → ℝ)
    (g : ∀ k, (J → Bool) → G k → ℝ)
    (S : I → Finset J) (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (X : I → (J → Bool) → ℝ)
    (hX : ∀ i ζ ζ', (∀ j ∈ S i, ζ j = ζ' j) → X i ζ = X i ζ')
    (R T ja v smooth : I → ℝ) (shift scale : I → K → ℝ) (owner : I → K)
    (hscale : ∀ i k, k ≠ owner i → scale i k = 0)
    (hshift : ∀ i k, shift i k ≠ 0 → P k i)
    (hκ : ∀ k (i : {i // P k i}), κ k (e k (Sum.inl i)) =
      scale i.val k ^ 2 * ja i.val ^ 2 * v i.val ^ 2)
    (hmean : ∀ i, independentSigns.expect (X i) = 0)
    (hvar : ∀ i, independentSigns.expect (fun ζ => X i ζ ^ 2) = v i) :
    independentSigns.expect (fun ζ => Walsh.resampleAverage (Finset.univ.biUnion S) (fun η =>
      ∑ s : I → Option K,
        (choiceBase (fun i => likelihood (R i) (T i) (ja i) (smooth i) (X i ζ)) s *
          ∏ i : ShiftPositions s, increment (R i.val) (T i.val) (ja i.val)
            (shift i.val (choiceSite s i)) (X i.val ζ)) *
        ∏ k, propensityPatternWeight (κ k) (W k) (u k)
          (completedSites (e k) (fun i => scale i.val k * X i.val ζ) (g k η)) η
          ((observationChoiceSet s k).image (slot k))) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage (Finset.univ.biUnion S) (fun η =>
      (∏ k, pointValue (torusProjection (u k))
        (completedSites (e k) (fun i => scale i.val k * X i.val ζ) (g k η)) η (W k)) *
        ∏ i, (likelihood (R i) (T i) (ja i) (smooth i) (X i ζ) +
          realField (R i) (T i) (ja i) (ja i * shift i (owner i) * scale i (owner i) * v i) (X i ζ))) ζ) := by
  have hδ (ζ : J → Bool) (i : I) (k : K)
      (hi : increment (R i) (T i) (ja i) (shift i k) (X i ζ) ≠ 0) : P k i := by
    apply hshift i k
    intro hs
    exact hi (by simp only [increment, hs, zero_mul])
  have hrows (ζ η : J → Bool) := retained_observation_rows P G e slot hslot κ scale ja v
    (fun i => X i ζ) hκ W u η (fun k => g k η)
    (fun i => likelihood (R i) (T i) (ja i) (smooth i) (X i ζ))
    (fun i k => increment (R i) (T i) (ja i) (shift i k) (X i ζ)) (hδ ζ)
  have hbase (ζ η : J → Bool) (k : K) := pointValue_retained_rows (P k) (e k)
    (fun i => scale i k) (fun i => X i ζ) (W k) (u k) η (g k η)
  simp_rw [hrows, hbase]
  exact assigned_shared_coefficient_matching
    (fun η k r => completedRowCoefficient (W k) (u k) η (e k) (g k η) r)
    (fun k r => retainedRowDegree (P k) (e k) r.1) S hS X hX R T ja v smooth shift scale owner hscale
    (fun i r => retainedRowDegree_le_one (P (owner i)) (e (owner i)) r.1 i) hmean hvar

end CausalLowerbound.PartC

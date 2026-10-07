import CausalLowerbound.PartC.ObservationBlockChoices
import CausalLowerbound.PartC.CrossBlockPatternRemoval
import CausalLowerbound.PartC.RetainedObservationSlots
import CausalLowerbound.PartC.GlobalPropensityShift

/-! Count the selected observation slots and absorb the normalization
exactly once per selected observation. Every nonzero physical term selects
only retained slots, as required by the ghost resampling estimates. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
variable {d I K V J G : Type*} [Fintype d] [DecidableEq d]
  [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J] [Fintype G]

theorem observationChoiceSet_sum_card (s : I → Option K) :
    (∑ k, (observationChoiceSet s k).card) = choiceDegree s := by
  have hc (i : I) : (∑ k : K, if s i = some k then (1 : ℕ) else 0) =
      if (s i).isSome then 1 else 0 := by
    cases h : s i with
    | none => simp [h]
    | some k => simp [h]
  simp only [observationChoiceSet, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [hc, choiceDegree, ShiftPositions, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem observationChoiceSet_nonzero (δ : I → K → ℝ) (s : I → Option K)
    (hs : (∏ i : ShiftPositions s, δ i.val (choiceSite s i)) ≠ 0)
    (k : K) (i : I) (hi : i ∈ observationChoiceSet s k) : δ i k ≠ 0 := by
  have hi' : s i = some k := (Finset.mem_filter.mp hi).2
  let j : ShiftPositions s := ⟨i, by simp only [hi', Option.isSome_some]⟩
  have hj : choiceSite s j = k := by simp [choiceSite, j, hi']
  have hh := Finset.prod_ne_zero_iff.mp hs j (Finset.mem_univ j)
  simpa only [hj, j] using hh

theorem observationChoiceSet_image_card (δ : I → K → ℝ) (slot : K → I → V)
    (hslot : ∀ k i j, δ i k ≠ 0 → δ j k ≠ 0 → slot k i = slot k j → i = j)
    (s : I → Option K) (hs : (∏ i : ShiftPositions s, δ i.val (choiceSite s i)) ≠ 0) (k : K) :
    ((observationChoiceSet s k).image (slot k)).card = (observationChoiceSet s k).card := by
  apply Finset.card_image_iff.mpr
  intro i hi j hj he
  exact hslot k i j (observationChoiceSet_nonzero δ s hs k i hi)
    (observationChoiceSet_nonzero δ s hs k j hj) he

theorem observation_pattern_normalization (amp N : ℝ) (δ : I → K → ℝ) (slot : K → I → V)
    (hslot : ∀ k i j, δ i k ≠ 0 → δ j k ≠ 0 → slot k i = slot k j → i = j)
    (κ : K → V → ℝ) (W : K → Array d V J 1) (u : K → V × d → ℝ)
    (z : K → V → ℝ) (ζ : J → Bool) (s : I → Option K) :
    (∏ i : ShiftPositions s, (amp * N) * δ i.val (choiceSite s i)) *
      (∏ k, propensityPatternWeight (κ k) (W k) (u k) (z k) ζ
        ((observationChoiceSet s k).image (slot k))) =
      amp ^ choiceDegree s * (∏ i : ShiftPositions s, δ i.val (choiceSite s i)) *
        propensityPatternProduct N κ W u z ζ (fun k => (observationChoiceSet s k).image (slot k)) := by
  by_cases hs : (∏ i : ShiftPositions s, δ i.val (choiceSite s i)) = 0
  · simp only [Finset.prod_mul_distrib, hs, mul_zero, zero_mul]
  have hcard : (∑ k, ((observationChoiceSet s k).image (slot k)).card) = choiceDegree s := by
    simp only [observationChoiceSet_image_card δ slot hslot s hs, observationChoiceSet_sum_card]
  simp only [propensityPatternProduct, weightedPropensityPatternWeight, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hcard, Finset.prod_const, Finset.card_univ, choiceDegree, mul_pow]
  ring

theorem mixedPropensityCellIncrement_nonzero_incident (x₀ : d → ℝ) (ℓ r h ja b : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ) (y : Bool × Bool)
    (k : d → ℤ) (amp : ℝ)
    (hx : mixedPropensityCellIncrement x₀ ℓ r h ja b ζ x y k amp ≠ 0) :
    x ∈ carrierBox x₀ r k := by
  apply linearPartition_nonzero_mem_carrierBox
  intro hp
  exact hx (by simp only [mixedPropensityCellIncrement, hp, mul_zero, zero_mul])

theorem physical_observation_pattern_retained (Q : ℕ) (hQ : 0 < Q)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h ja b : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool)
    (amp : S → ℝ) (s : I → Option S)
    (hs : (∏ i : ShiftPositions s, mixedPropensityCellIncrement x₀ ℓ r h ja b ζ
      (x i.val) (y i.val) (choiceSite s i).val (amp (choiceSite s i))) ≠ 0)
    (k : S) (e : {i // x i ∈ carrierBox x₀ r k.val} ⊕ G ≃ Fin Q)
    (v : Fin Q) (hv : v ∈ (observationChoiceSet s k).image (retainedObservationSlot Q hQ x₀ r k.val x e)) :
    ∃ i : {i // x i ∈ carrierBox x₀ r k.val}, e (Sum.inl i) = v := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  have hn : mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i) (y i) k.val (amp k) ≠ 0 :=
    observationChoiceSet_nonzero (I := I) (K := S)
      (fun (i : I) (k : S) => mixedPropensityCellIncrement x₀ ℓ r h ja b ζ (x i) (y i) k.val (amp k))
      s (by exact hs) k i hi
  have hx := mixedPropensityCellIncrement_nonzero_incident x₀ ℓ r h ja b ζ (x i) (y i) k.val (amp k) hn
  exact ⟨⟨i, hx⟩, (retainedObservationSlot_incident Q hQ x₀ r k.val x e i hx).symm⟩

end CausalLowerbound.PartC

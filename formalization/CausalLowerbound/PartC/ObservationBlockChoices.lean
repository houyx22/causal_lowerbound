import CausalLowerbound.PartC.BlockPatternFunctional

/-! Expand an affine likelihood by assigning each observation either to
its baseline or to one perturbation block. The selected observation sets
are disjoint. Slot injectivity is needed only where the shift is nonzero. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB MvPolynomial
variable {I K V : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

def observationChoiceSlot (slot : K → I → V) (s : I → Option K)
    (i : ShiftPositions s) : K × V := (choiceSite s i, slot (choiceSite s i) i.val)

def observationChoiceSet (s : I → Option K) (k : K) : Finset I :=
  Finset.univ.filter (fun i => s i = some k)

theorem choiceSite_some (s : I → Option K) (i : ShiftPositions s) :
    s i.val = some (choiceSite s i) := by
  have hi := i.property
  cases h : s i.val with
  | none => simp only [h, Option.isSome_none, Bool.false_eq_true] at hi
  | some k => simp [choiceSite, h]

theorem observationChoiceSet_disjoint (s : I → Option K) (k l : K) (hkl : k ≠ l) :
    Disjoint (observationChoiceSet s k) (observationChoiceSet s l) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [observationChoiceSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact hkl (Option.some.inj (hi.symm.trans hj))

theorem observationChoiceSlot_slice (slot : K → I → V) (s : I → Option K) (k : K) :
    blockSiteSet (Finset.univ.image (observationChoiceSlot slot s)) k =
      (observationChoiceSet s k).image (slot k) := by
  ext v
  simp only [mem_blockSiteSet, Finset.mem_image, Finset.mem_univ, true_and,
    observationChoiceSet, Finset.mem_filter]
  constructor
  · rintro ⟨i, hi⟩
    have hk : choiceSite s i = k := congrArg Prod.fst hi
    have hv : slot (choiceSite s i) i.val = v := congrArg Prod.snd hi
    exact ⟨i.val, by rw [choiceSite_some s i, hk], by simpa only [hk] using hv⟩
  · rintro ⟨i, hi, hv⟩
    let j : ShiftPositions s := ⟨i, by simp only [hi, Option.isSome_some]⟩
    have hj : choiceSite s j = k := by simp [choiceSite, j, hi]
    refine ⟨j, ?_⟩
    change (choiceSite s j, slot (choiceSite s j) i) = (k, v)
    rw [hj, hv]

theorem observation_choice_polynomial (base : I → ℝ) (δ : I → K → ℝ)
    (slot : K → I → V) :
    (∏ i, (C (base i) + ∑ k, C (δ i k) * X (k, slot k i))) =
      ∑ s : I → Option K,
        C (choiceBase base s * ∏ i : ShiftPositions s, δ i.val (choiceSite s i)) *
          ∏ i : ShiftPositions s, X (observationChoiceSlot slot s i) := by
  apply MvPolynomial.funext
  intro z
  simp only [map_prod, map_add, map_sum, map_mul, eval_C, eval_X]
  rw [shifted_product_expansion]
  apply Finset.sum_congr rfl
  intro s _
  rw [choiceValue_split, Finset.prod_mul_distrib]
  exact (mul_assoc _ _ _).symm

theorem sitePatternFunctional_observation_choices (w : Finset (K × V) → ℝ)
    (base : I → ℝ) (δ : I → K → ℝ) (slot : K → I → V) :
    sitePatternFunctional w (∏ i, (C (base i) + ∑ k, C (δ i k) * X (k, slot k i))) =
      ∑ s : I → Option K, if Function.Injective (observationChoiceSlot slot s) then
        (choiceBase base s * ∏ i : ShiftPositions s, δ i.val (choiceSite s i)) *
          w (Finset.univ.image (observationChoiceSlot slot s)) else 0 := by
  rw [observation_choice_polynomial, map_sum]
  simp only [MvPolynomial.C_mul', map_smul, smul_eq_mul, sitePatternFunctional_prod_X,
    mul_ite, mul_zero]

theorem observationChoiceSlot_injective (δ : I → K → ℝ) (slot : K → I → V)
    (hslot : ∀ k i j, δ i k ≠ 0 → δ j k ≠ 0 → slot k i = slot k j → i = j)
    (s : I → Option K) (hs : (∏ i : ShiftPositions s, δ i.val (choiceSite s i)) ≠ 0) :
    Function.Injective (observationChoiceSlot slot s) := by
  have hd (i : ShiftPositions s) : δ i.val (choiceSite s i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hs i (Finset.mem_univ i)
  intro i j hij
  have hk : choiceSite s i = choiceSite s j := congrArg Prod.fst hij
  have hv : slot (choiceSite s i) i.val = slot (choiceSite s j) j.val := congrArg Prod.snd hij
  apply Subtype.ext
  apply hslot (choiceSite s i) i.val j.val (hd i)
  · rw [hk]
    exact hd j
  · simpa only [hk] using hv

theorem block_site_observation_expansion (w : K → Finset V → ℝ)
    (base : I → ℝ) (δ : I → K → ℝ) (slot : K → I → V)
    (hslot : ∀ k i j, δ i k ≠ 0 → δ j k ≠ 0 → slot k i = slot k j → i = j) :
    sitePatternFunctional (fun S => ∏ k, w k (blockSiteSet S k))
        (∏ i, (C (base i) + ∑ k, C (δ i k) * X (k, slot k i))) =
      ∑ s : I → Option K,
        (choiceBase base s * ∏ i : ShiftPositions s, δ i.val (choiceSite s i)) *
          ∏ k, w k ((observationChoiceSet s k).image (slot k)) := by
  rw [sitePatternFunctional_observation_choices]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : (∏ i : ShiftPositions s, δ i.val (choiceSite s i)) = 0
  · simp only [hs, mul_zero, zero_mul, ite_self]
  · rw [if_pos (observationChoiceSlot_injective δ slot hslot s hs)]
    simp only [observationChoiceSlot_slice]

end CausalLowerbound.PartC

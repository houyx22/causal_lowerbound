import CausalLowerbound.PartC.RepresentativeFactors
import CausalLowerbound.PartC.WalshRemoval

/-! Exact locality of evaluation when all excluded symbol projections
vanish. This does not assume any independence of the evaluated fields. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC

namespace Walsh
variable {J : Type*} [Fintype J] [DecidableEq J]

def freezeOutside (T : Finset J) (ζ : J → Bool) (j : J) : Bool :=
  if j ∈ T then ζ j else false

theorem freezeOutside_congr (T : Finset J) (ζ ζ' : J → Bool)
    (hζ : ∀ j ∈ T, ζ j = ζ' j) : freezeOutside T ζ = freezeOutside T ζ' := by
  funext j
  by_cases hj : j ∈ T <;> simp [freezeOutside, hj, hζ]

theorem evaluate_local_congr (T : Finset J) (a : Coefficients J)
    (ha : ∀ j ∉ T, symbolPart j a = 0) (ζ ζ' : J → Bool)
    (hζ : ∀ j ∈ T, ζ j = ζ' j) : evaluate ζ a = evaluate ζ' a := by
  simp only [evaluate_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S ⊆ T
  · rw [character_congr S ζ ζ' (fun j hj => hζ j (hS hj))]
  · obtain ⟨j, hjS, hjT⟩ := Finset.not_subset.mp hS
    have hz := congrArg (fun b : Coefficients J => b S) (ha j hjT)
    have haS : a S = 0 := by
      simpa only [symbolPart_apply, if_pos hjS, lp.coeFn_zero, Pi.zero_apply] using hz
    simp only [haS, zero_mul]

end Walsh

namespace Representative
variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

theorem factorValue_local_congr (T : Finset J) (a : Factor d J D)
    (ha : ∀ j ∉ T, factorSymbol j a = 0) (x : Wiener.Torus d) (z : ℝ)
    (ζ ζ' : J → Bool) (hζ : ∀ j ∈ T, ζ j = ζ' j) :
    factorValue x z ζ a = factorValue x z ζ' a := by
  unfold factorValue
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : r.2 ⊆ T
  · rw [Walsh.character_congr r.2 ζ ζ' (fun j hj => hζ j (hr hj))]
  · obtain ⟨j, hjr, hjT⟩ := Finset.not_subset.mp hr
    have hz := congrArg (fun b : Factor d J D => b r) (ha j hjT)
    have har : a r = 0 := by
      simpa only [factorSymbol_apply, if_pos hjr, lp.coeFn_zero, Pi.zero_apply] using hz
    simp only [har, map_zero, ContinuousMap.zero_apply, smul_zero]

theorem character_coefficient_local_congr (T : Finset J) (a : Array d ι J D)
    (ha : ∀ j ∉ T, symbolPart j a = 0) (r : Row ι J D) (x : Wiener.Torus (ι × d))
    (ζ ζ' : J → Bool) (hζ : ∀ j ∈ T, ζ j = ζ' j) :
    Walsh.character r.2 ζ * (Wiener.toContinuous (a r) x).re =
      Walsh.character r.2 ζ' * (Wiener.toContinuous (a r) x).re := by
  by_cases hr : r.2 ⊆ T
  · rw [Walsh.character_congr r.2 ζ ζ' (fun j hj => hζ j (hr hj))]
  · obtain ⟨j, hjr, hjT⟩ := Finset.not_subset.mp hr
    have hz := congrArg (fun b : Array d ι J D => b r) (ha j hjT)
    have har : a r = 0 := by
      simpa only [symbolPart_apply, if_pos hjr, lp.coeFn_zero, Pi.zero_apply] using hz
    simp only [har, map_zero, ContinuousMap.zero_apply, Complex.zero_re, mul_zero]

theorem pointValue_local_congr (T : Finset J) (a : Array d ι J D)
    (ha : ∀ j ∉ T, symbolPart j a = 0) (x : Wiener.Torus (ι × d)) (z : ι → ℝ)
    (ζ ζ' : J → Bool) (hζ : ∀ j ∈ T, ζ j = ζ' j) :
    pointValue x z ζ a = pointValue x z ζ' a := by
  simp only [pointValue, rowWeight, mul_assoc]
  apply Finset.sum_congr rfl
  intro r _
  rw [character_coefficient_local_congr T a ha r x ζ ζ' hζ]

end Representative
end CausalLowerbound.PartC

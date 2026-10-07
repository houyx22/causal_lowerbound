import CausalLowerbound.PartC.CubicObservationChoiceBounds

/-! Separate the unique zero-degree observation choice. It reproduces
the full design baseline; every remaining choice has positive degree. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Representative
variable {I K V : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

def cubicZeroChoice : I → CubicObservationChoice K :=
  fun _ => ⟨0, Fin.elim0⟩

theorem cubicObservationChoiceDegree_zero_choice :
    cubicObservationChoiceDegree (cubicZeroChoice : I → CubicObservationChoice K) = 0 := by
  rw [cubicObservationChoiceDegree_zero_iff]
  intro i
  rfl

theorem cubicObservationChoiceDegree_zero_eq (s : I → CubicObservationChoice K)
    (hs : cubicObservationChoiceDegree s = 0) : s = cubicZeroChoice := by
  funext i
  have hi := (cubicObservationChoiceDegree_zero_iff s).mp hs i
  rcases hsi : s i with ⟨n, f⟩
  rw [hsi] at hi
  change n = 0 at hi
  subst n
  change (⟨0, f⟩ : CubicObservationChoice K) = ⟨0, Fin.elim0⟩
  apply congrArg (fun g : Fin 0 → K => (⟨0, g⟩ : CubicObservationChoice K))
  funext j
  exact j.elim0

theorem cubicObservationChoiceDegree_pos_of_ne_zero (s : I → CubicObservationChoice K)
    (hs : s ≠ cubicZeroChoice) : 0 < cubicObservationChoiceDegree s :=
  Nat.pos_of_ne_zero (fun h => hs (cubicObservationChoiceDegree_zero_eq s h))

def cubicObservationTerm (w : K → Degree V 3 → ℝ)
    (b : I → Fin 4 → ℝ) (δ : I → K → ℝ) (slot : K → I → V) (amp : ℝ)
    (s : I → CubicObservationChoice K) : ℝ :=
  if hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3 then
    amp ^ cubicObservationChoiceDegree s *
      ((∏ i, b i (s i).1) * cubicObservationChoiceWeight δ s) *
        ∏ k, w k (fun v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v))
  else 0

theorem cubicObservationTerm_zero (w : K → Degree V 3 → ℝ)
    (b : I → Fin 4 → ℝ) (δ : I → K → ℝ) (slot : K → I → V) (amp : ℝ) :
    cubicObservationTerm w b δ slot amp cubicZeroChoice = (∏ i, b i 0) * ∏ k, w k 0 := by
  letI : IsEmpty (CubicObservationPositions (cubicZeroChoice : I → CubicObservationChoice K)) :=
    ⟨fun p => Fin.elim0 p.2⟩
  have hz : siteOccurrenceExponent
      (cubicObservationChoiceSlot slot (cubicZeroChoice : I → CubicObservationChoice K)) = 0 := by
    ext v
    simp [siteOccurrenceExponent_apply, Finset.univ_eq_empty]
  have hw : cubicObservationChoiceWeight δ (cubicZeroChoice : I → CubicObservationChoice K) = 1 := by
    apply Finset.prod_eq_one
    intro p _
    exact isEmptyElim p
  simp [cubicObservationTerm, hz, cubicObservationChoiceDegree_zero_choice,
    hw, cubicZeroChoice, cubicSiteDegree, Pi.zero_def]

theorem cubicObservationExpansion_baseline (w : K → Degree V 3 → ℝ)
    (b : I → Fin 4 → ℝ) (δ : I → K → ℝ) (slot : K → I → V) (amp : ℝ) :
    cubicObservationExpansion w b δ slot amp = (∏ i, b i 0) * (∏ k, w k 0) +
      ∑ s ∈ Finset.univ.erase cubicZeroChoice, cubicObservationTerm w b δ slot amp s := by
  change (∑ s, cubicObservationTerm w b δ slot amp s) = _
  have he := Finset.sum_erase_add Finset.univ (cubicObservationTerm w b δ slot amp)
    (Finset.mem_univ (cubicZeroChoice : I → CubicObservationChoice K))
  rw [cubicObservationTerm_zero] at he
  exact he.symm.trans (add_comm _ _)

end CausalLowerbound.PartC

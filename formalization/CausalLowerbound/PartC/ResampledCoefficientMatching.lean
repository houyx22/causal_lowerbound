import CausalLowerbound.PartC.AssignedCoefficientMatching
import CausalLowerbound.PartC.RemovedPropensityMatching
import CausalLowerbound.PartC.ResamplingParity

/-! Exact matching after resampling the union of the retained local sign
sets. One shared fresh field supplies all carrier coefficients. Independent
copies are used only for the disjoint retained rough fields, with the
identity derived from the actual finite sign law. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB RoughPropensity
variable {I K J : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]

theorem resampled_disjoint_sign_matching {A : Type*}
    (S : I → Finset J) (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (X : I → (J → Bool) → A)
    (hX : ∀ i ζ ζ', (∀ j ∈ S i, ζ j = ζ' j) → X i ζ = X i ζ')
    (f g : (J → Bool) → (I → A) → ℝ)
    (hmatch : ∀ η,
      (FiniteLaw.independent (fun _ : I => independentSigns (ι := J))).expect
        (fun fresh => f η (fun i => X i (fresh i))) =
      (FiniteLaw.independent (fun _ : I => independentSigns (ι := J))).expect
        (fun fresh => g η (fun i => X i (fresh i)))) :
    independentSigns.expect (fun ζ => Walsh.resampleAverage (Finset.univ.biUnion S)
      (fun η => f η (fun i => X i ζ)) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage (Finset.univ.biUnion S)
      (fun η => g η (fun i => X i ζ)) ζ) := by
  let T := Finset.univ.biUnion S
  have hout (ζ ζ' : J → Bool) (h : ∀ j, (∀ i, j ∉ S i) → ζ j = ζ' j) :
      ∀ j ∉ T, ζ j = ζ' j := by
    intro j hj
    apply h j
    intro i hi
    exact hj (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩)
  apply disjoint_sign_matching S hS X hX
    (fun ζ v => Walsh.resampleAverage T (fun η => f η v) ζ)
    (fun ζ v => Walsh.resampleAverage T (fun η => g η v) ζ)
  · intro ζ ζ' v he
    exact Walsh.resampleAverage_congr_outside T _ ζ ζ' (hout ζ ζ' he)
  · intro ζ ζ' v he
    exact Walsh.resampleAverage_congr_outside T _ ζ ζ' (hout ζ ζ' he)
  · intro base
    unfold Walsh.resampleAverage
    rw [FiniteLaw.expect_comm, FiniteLaw.expect_comm
      (FiniteLaw.independent (fun _ : I => independentSigns (ι := J))) independentSigns]
    apply FiniteLaw.expect_congr
    intro η
    exact hmatch (Walsh.resample T base η)

theorem assigned_shared_coefficient_matching
    {Rows : K → Type*} [∀ k, Fintype (Rows k)]
    (coeff : (J → Bool) → ∀ k, Rows k → ℝ) (degree : ∀ k, Rows k → I → ℕ)
    (S : I → Finset J) (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (X : I → (J → Bool) → ℝ)
    (hX : ∀ i ζ ζ', (∀ j ∈ S i, ζ j = ζ' j) → X i ζ = X i ζ')
    (R T ja v smooth : I → ℝ) (shift scale : I → K → ℝ) (owner : I → K)
    (hscale : ∀ i k, k ≠ owner i → scale i k = 0)
    (he : ∀ i r, degree (owner i) r i ≤ 1)
    (hmean : ∀ i, independentSigns.expect (X i) = 0)
    (hvar : ∀ i, independentSigns.expect (fun ζ => X i ζ ^ 2) = v i) :
    independentSigns.expect (fun ζ => Walsh.resampleAverage (Finset.univ.biUnion S) (fun η =>
      ∑ s : I → Option K,
        (choiceBase (fun i => likelihood (R i) (T i) (ja i) (smooth i) (X i ζ)) s *
          ∏ i : ShiftPositions s, increment (R i.val) (T i.val) (ja i.val)
            (shift i.val (choiceSite s i)) (X i.val ζ)) *
          ∏ k, ∑ r, coeff η k r * ∏ i, if s i = some k then
            normalizedSubstitution (degree k r i) (scale i k) (ja i) (v i) (X i ζ)
            else (scale i k * X i ζ) ^ degree k r i) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage (Finset.univ.biUnion S) (fun η =>
      (∏ k, ∑ r, coeff η k r * ∏ i, (scale i k * X i ζ) ^ degree k r i) *
        ∏ i, (likelihood (R i) (T i) (ja i) (smooth i) (X i ζ) +
          realField (R i) (T i) (ja i) (ja i * shift i (owner i) * scale i (owner i) * v i) (X i ζ))) ζ) := by
  apply resampled_disjoint_sign_matching S hS X hX
    (fun η z => ∑ s : I → Option K,
      (choiceBase (fun i => likelihood (R i) (T i) (ja i) (smooth i) (z i)) s *
        ∏ i : ShiftPositions s, increment (R i.val) (T i.val) (ja i.val)
          (shift i.val (choiceSite s i)) (z i.val)) *
        ∏ k, ∑ r, coeff η k r * ∏ i, if s i = some k then
          normalizedSubstitution (degree k r i) (scale i k) (ja i) (v i) (z i)
          else (scale i k * z i) ^ degree k r i)
    (fun η z => (∏ k, ∑ r, coeff η k r * ∏ i, (scale i k * z i) ^ degree k r i) *
      ∏ i, (likelihood (R i) (T i) (ja i) (smooth i) (z i) +
        realField (R i) (T i) (ja i) (ja i * shift i (owner i) * scale i (owner i) * v i) (z i)))
  intro η
  exact assigned_coefficient_pattern_matching (coeff η) degree
    (fun _ : I => independentSigns (ι := J)) X R T ja v smooth shift scale owner hscale he hmean hvar

end CausalLowerbound.PartC

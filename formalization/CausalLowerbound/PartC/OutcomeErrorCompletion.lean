import CausalLowerbound.PartC.OutcomeObservationComparison
import CausalLowerbound.PartC.GhostDefectReindex

/-! The cubic comparison budget is independent of completion labels.
Consequently the finite slot-permutation average adds no further cost. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem outcomeObservationComparisonError_completion
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ a jb t τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e e' : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G e =
      outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G e' := by
  have he (k : S) : completedGhostTaperDefect Q (e k) τ
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) =
      completedGhostTaperDefect Q (e' k) τ
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) := by
    simpa only [Function.comp_def, Equiv.refl_apply] using completedGhostTaperDefect_reindex Q τ
      (e k) (e' k) (Equiv.refl _) (Equiv.refl _)
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
  simp only [outcomeObservationComparisonError, outcomeObservationTaperCost, he]

theorem outcomeObservationComparisonError_permutation_average
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ a jb t τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (fun σ =>
      outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G (fun k => (e k).trans (σ k).symm)) =
      outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G e := by
  calc
    _ = (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (fun _ =>
        outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G e) :=
      FiniteLaw.expect_congr _ (fun σ => outcomeObservationComparisonError_completion
        Q S x₀ ℓ r h c N N₀ a jb t τ B x G _ e)
    _ = _ := FiniteLaw.expect_const _ _

theorem outcomeObservationComparisonError_nonneg
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ a jb t τ : ℝ)
    (hℓ : 0 ≤ ℓ) (hr : 0 ≤ r) (hc : 0 ≤ c) (hN : 0 ≤ N) (hN₀ : 0 ≤ N₀)
    (hjb : 0 ≤ jb) (hshift : 0 ≤ a * t)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    0 ≤ outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G e := by
  let T := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))
  have hA := outcomeObservationSignCost_nonneg Q S ℓ r h c N N₀ hℓ hr hc hN B G T
  have hD := outcomeObservationTaperCost_nonneg Q S x₀ r c N₀ τ x G e
  have hs := outcomeObservationScalarScale_nonneg (Fintype.card I) N₀ jb (a * t) hN₀ hjb hshift
  unfold outcomeObservationComparisonError
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (add_nonneg hA hD) hs))
    (mul_nonneg hA (by positivity))

end CausalLowerbound.PartC

import CausalLowerbound.PartC.PhysicalCompletedOutcomeMatching
import CausalLowerbound.PartC.BlockFunctionalShift

/-! The physical completed outcome identity also includes empty carried
block sets. Coverage then forces the coarse envelope and target to vanish. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative MvPolynomial RoughOutcome
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem physical_completed_outcome_matching
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N a jb t : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hw : 0 < w) (hw1 : w ≤ 1) (hN : N ≠ 0)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (x : I → d → ℝ) (R T smooth : I → ℝ)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ghost : ∀ k, G k → d → ℝ) :
    let u := fun k : S => completedConfiguration (e k)
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)
    let z := fun (ζ η : activeBlocks (d := d) ℓ h → Bool) (k : S) => completedSites (e k)
      (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
        (carrierCoordinate (localCoordinate x₀ r k.val (x i.val))))
      (fun j => normalizedRoughChart x₀ ℓ r h k.val c w N η (ghost k j))
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      blockPolynomialFunctional (fun k => outcomePolynomialFunctional
        (fun v => normalizedRoughVariance x₀ r h k.val c w N (configurationSite (u k) v))
        (B k) (u k) (z ζ η k) η)
        (∏ i, outcomeTaylorPolynomial (R i) (T i) 1 jb
          (physicalRoughCorrection x₀ ℓ h (a * t) (x i)) (smooth i)
          (physicalRoughField x₀ ℓ h ζ (x i))
          (∑ k : S, C ((a * linearPartition (localCoordinate x₀ r k.val (x i))) * (t * N)) *
            X (k, retainedObservationSlot Q hQ x₀ r k.val x (e k) i)))) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      (∏ k, pointValue (torusProjection (u k)) (z ζ η k) η (B k)) *
        ∏ i, (likelihood (R i) (T i) jb (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
          (smooth i) (physicalRoughField x₀ ℓ h ζ (x i)) +
            realField (R i) (T i) (smooth i) (targetField x₀ h (a * t * jb) (x i)))) ζ) := by
  by_cases hS : IsEmpty S
  · letI := hS
    dsimp only
    have hG (i : I) : coarseBump x₀ h (x i) = 0 := by
      by_contra hi
      obtain ⟨k, hk, _⟩ := assignment_exists_unique S w hw hw1 x₀ r hr (x i)
        (hcover i hi) (htr i hi)
      exact isEmptyElim (⟨k, hk.1⟩ : S)
    have htarget (i : I) : targetField x₀ h (a * t * jb) (x i) = 0 := by
      simp only [targetField, hG i, zero_pow (by decide : 2 ≠ 0), mul_zero]
    apply FiniteLaw.expect_congr
    intro ζ
    unfold Walsh.resampleAverage
    apply FiniteLaw.expect_congr
    intro fresh
    simp only [blockPolynomialFunctional_isEmpty, map_prod, outcomeTaylorPolynomial_eval,
      Finset.sum_of_isEmpty, Finset.prod_of_isEmpty, map_zero, one_mul, mul_zero,
      add_zero, htarget, realField, zero_mul]
  · haveI : Nonempty S := by
      by_contra hn
      exact hS ⟨fun k => hn ⟨k⟩⟩
    exact physical_completed_outcome_matching_nonempty Q hQ S x₀ ℓ r h c w N a jb t
      hℓ hr hh hw hw1 hN hm x R T smooth hsep hcover htr B G e ghost

end CausalLowerbound.PartC


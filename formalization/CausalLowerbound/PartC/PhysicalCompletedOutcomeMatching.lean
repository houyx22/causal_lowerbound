import CausalLowerbound.PartC.CompletedOutcomeMatching
import CausalLowerbound.PartC.RetainedTaylorPolynomial
import CausalLowerbound.PartC.SupportedOutcomeAssignment
import CausalLowerbound.PartC.PhysicalLocalOutcomeMatching

/-! Completed cubic matching for the actual physical rough-outcome
field. The assignment geometry, second and fourth moments, and effective
shift are all supplied by the construction. The resulting target keeps
the original amplitude a*t*jb. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative MvPolynomial RoughOutcome
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem physical_completed_outcome_matching_nonempty
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) [Nonempty S]
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
  dsimp only
  obtain ⟨owner, hscale, heffective, hamp⟩ := exists_supported_outcome_parameters S x₀ r h c w N a jb t
    hr hw hw1 hN hm x hcover htr
  have hshift (i : I) (k : S)
      (hi : (a * linearPartition (localCoordinate x₀ r k.val (x i))) * (t * N) ≠ 0) :
      x i ∈ carrierBox x₀ r k.val := by
    apply linearPartition_nonzero_mem_carrierBox
    intro hp
    exact hi (by rw [hp, mul_zero, zero_mul])
  have he := completed_resampled_outcome_matching
    (fun k : S => fun i : I => x i ∈ carrierBox x₀ r k.val) G e
    (fun k v => normalizedRoughVariance x₀ r h k.val c w N
      (configurationSite (completedConfiguration (e k)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)) v))
    B (fun k => completedConfiguration (e k)
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k))
    (fun k η j => normalizedRoughChart x₀ ℓ r h k.val c w N η (ghost k j))
    (fun i => physicalLocalSigns x₀ ℓ h (x i))
    (fun i j hij => physicalLocalSigns_disjoint x₀ ℓ h hℓ (x i) (x j) (hsep i j hij))
    (fun i ζ => physicalRoughField x₀ ℓ h ζ (x i))
    (fun i ζ ζ' hi => physicalRoughField_local_congr x₀ ℓ h (x i) ζ ζ' hi)
    R T (fun _ => jb) (fun i => physicalRoughCorrection x₀ ℓ h (a * t) (x i))
    (fun i => coarseBump x₀ h (x i) ^ 2) smooth
    (fun i k => (a * linearPartition (localCoordinate x₀ r k.val (x i))) * (t * N))
    (fun i k => supportedAssignmentScale x₀ r h c w N k.val (x i)) owner hscale
    (fun k i hi => supportedAssignmentScale_zero_of_not_incident x₀ r h c w N hw hw1 k.val (x i) hi)
    (fun k i => normalizedRoughVariance_completed_retained x₀ r h hr.ne' k.val c w N x (e k) (ghost k) i)
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).1)
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).2.1)
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).2.2.1)
    (fun i => physicalRoughCorrection_zero_or_shift x₀ ℓ h
      (((a * linearPartition (localCoordinate x₀ r (owner i).val (x i))) * (t * N)) *
        supportedAssignmentScale x₀ r h c w N (owner i).val (x i)) (a * t) jb hℓ hh (x i)
      ((heffective i).imp_right Or.inr))
  simpa only [blockPolynomialMap_observation_taylor _ G e
    (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k))
    (fun k i hi => retainedObservationSlot_incident Q hQ x₀ r k.val x (e k) i hi)
    R T (fun _ => jb) _ smooth _ _ hshift,
    normalizedRoughChart_local x₀ ℓ r h hr.ne', supportedAssignmentScale_rough, hamp] using he

end CausalLowerbound.PartC

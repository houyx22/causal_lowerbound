import CausalLowerbound.PartC.CompletedSharedMatching
import CausalLowerbound.PartC.SupportedAssignment
import CausalLowerbound.PartC.PhysicalLocalSigns

/-! Instantiate completed shared-sign matching at the actual physical
observations. The rough moments and disjoint sign sets are proved from
spatial separation; the assignment interior supplies the owner and the
original target amplitude. No carrier matching hypothesis is assumed. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative RoughPropensity
variable {d I G V : Type*} [Fintype d] [DecidableEq d]
  [Fintype I] [DecidableEq I] [Fintype G] [Fintype V]

theorem carrierCoordinate_rescale (y : d → ℝ) :
    (fun j => 4 * carrierCoordinate y j - 2) = y := by
  funext j
  simp only [carrierCoordinate]
  ring

theorem roughChartPoint_carrierCoordinate_local (x₀ : d → ℝ) (r : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (x : d → ℝ) :
    roughChartPoint x₀ r k (carrierCoordinate (localCoordinate x₀ r k x)) = x := by
  funext j
  simp only [roughChartPoint, carrierCoordinate, localCoordinate]
  field_simp
  <;> ring

theorem normalizedRoughChart_local (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ) :
    normalizedRoughChart x₀ ℓ r h k c w N ζ (carrierCoordinate (localCoordinate x₀ r k x)) =
      (assignmentMultiplier c w (localCoordinate x₀ r k x) / N) * physicalRoughField x₀ ℓ h ζ x := by
  rw [normalizedRoughChart_eq_scale, carrierCoordinate_rescale,
    roughChartPoint_carrierCoordinate_local x₀ r hr k x]

theorem physicalPropensitySlotCorrection_completed_retained
    (x₀ : d → ℝ) (r h : ℝ) (hr : r ≠ 0) (k : d → ℤ) (c w N ja : ℝ)
    (x : I → d → ℝ) (e : {i // x i ∈ carrierBox x₀ r k} ⊕ G ≃ V)
    (ghost : G → d → ℝ) (i : {i // x i ∈ carrierBox x₀ r k}) :
    physicalPropensitySlotCorrection x₀ r h k c w N ja
      (completedConfiguration e (fun j => carrierCoordinate (localCoordinate x₀ r k (x j.val))) ghost)
      (e (Sum.inl i)) =
        (assignmentMultiplier c w (localCoordinate x₀ r k (x i.val)) / N) ^ 2 * ja ^ 2 *
          (coarseBump x₀ h (x i.val) ^ 2) ^ 2 := by
  rw [physicalPropensitySlotCorrection_eq_variance]
  simp only [completedConfiguration, completedSites_retained]
  rw [carrierCoordinate_rescale, roughChartPoint_carrierCoordinate_local x₀ r hr k (x i.val)]

theorem physical_completed_shared_pattern_matching
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N ja b t : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hw : 0 < w) (hw1 : w ≤ 1) (hN : N ≠ 0)
    (hm : ∀ y : d → ℝ, assignmentMultiplier c w y * linearPartition y = assignmentPartition w y)
    (x : I → d → ℝ) (R T smooth : I → ℝ)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
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
      ∑ s : I → Option S,
        (choiceBase (fun i => likelihood (R i) (T i) ja (smooth i) (physicalRoughField x₀ ℓ h ζ (x i))) s *
          ∏ i : ShiftPositions s, increment (R i.val) (T i.val) ja
            ((b * linearPartition (localCoordinate x₀ r (choiceSite s i).val (x i.val))) * (t * N))
            (physicalRoughField x₀ ℓ h ζ (x i.val))) *
        ∏ k, propensityPatternWeight (physicalPropensitySlotCorrection x₀ r h k.val c w N ja (u k))
          (B k) (u k) (z ζ η k) η
          ((observationChoiceSet s k).image (retainedObservationSlot Q hQ x₀ r k.val x (e k)))) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      (∏ k, pointValue (torusProjection (u k)) (z ζ η k) η (B k)) *
        ∏ i, (likelihood (R i) (T i) ja (smooth i) (physicalRoughField x₀ ℓ h ζ (x i)) +
          realField (R i) (T i) ja (targetField x₀ h (ja * b * t) (x i))
            (physicalRoughField x₀ ℓ h ζ (x i)))) ζ) := by
  dsimp only
  by_cases hS : IsEmpty S
  · letI := hS
    have hG (i : I) : coarseBump x₀ h (x i) = 0 := by
      by_contra hi
      obtain ⟨k, hk, _⟩ := assignment_exists_unique S w hw hw1 x₀ r hr (x i) (hcover i hi) (htr i hi)
      exact isEmptyElim (⟨k, hk.1⟩ : S)
    have htarget (i : I) : targetField x₀ h (ja * b * t) (x i) = 0 := by
      simp only [targetField, hG i, zero_pow (by decide : 2 ≠ 0), mul_zero]
    apply FiniteLaw.expect_congr
    intro ζ
    unfold Walsh.resampleAverage
    apply FiniteLaw.expect_congr
    intro fresh
    simp only [Finset.prod_of_isEmpty, one_mul, mul_one, htarget, realField,
      mul_zero, zero_mul, add_zero]
    have he := shifted_product_expansion
      (fun i => likelihood (R i) (T i) ja (smooth i) (physicalRoughField x₀ ℓ h ζ (x i)))
      (fun (i : I) (k : S) => increment (R i) (T i) ja
        ((b * linearPartition (localCoordinate x₀ r k.val (x i))) * (t * N))
        (physicalRoughField x₀ ℓ h ζ (x i)))
    simpa only [choiceValue_split, Finset.sum_of_isEmpty, add_zero] using he.symm
  haveI : Nonempty S := by
    by_contra hn
    exact hS ⟨fun k => hn ⟨k⟩⟩
  obtain ⟨owner, hscale, hamp⟩ := exists_supported_assigned_parameters S x₀ r h c w N ja b t
    hr hw hw1 hN hm x hcover htr
  have hshift (i : I) (k : S)
      (hi : (b * linearPartition (localCoordinate x₀ r k.val (x i))) * (t * N) ≠ 0) :
      x i ∈ carrierBox x₀ r k.val := by
    apply linearPartition_nonzero_mem_carrierBox
    intro hp
    exact hi (by rw [hp, mul_zero, zero_mul])
  have he := completed_shared_pattern_matching
    (fun k : S => fun i : I => x i ∈ carrierBox x₀ r k.val) G e
    (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k))
    (fun k i hi => retainedObservationSlot_incident Q hQ x₀ r k.val x (e k) i hi)
    (fun k => physicalPropensitySlotCorrection x₀ r h k.val c w N ja
      (completedConfiguration (e k) (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k)))
    B (fun k => completedConfiguration (e k)
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) (ghost k))
    (fun k η j => normalizedRoughChart x₀ ℓ r h k.val c w N η (ghost k j))
    (fun i => physicalLocalSigns x₀ ℓ h (x i))
    (fun i j hij => physicalLocalSigns_disjoint x₀ ℓ h hℓ (x i) (x j) (hsep i j hij))
    (fun i ζ => physicalRoughField x₀ ℓ h ζ (x i))
    (fun i ζ ζ' hi => physicalRoughField_local_congr x₀ ℓ h (x i) ζ ζ' hi)
    R T (fun _ => ja) (fun i => coarseBump x₀ h (x i) ^ 2) smooth
    (fun i k => (b * linearPartition (localCoordinate x₀ r k.val (x i))) * (t * N))
    (fun i k => supportedAssignmentScale x₀ r h c w N k.val (x i))
    owner hscale hshift
    (fun k i => (physicalPropensitySlotCorrection_completed_retained x₀ r h hr.ne' k.val c w N ja x (e k) (ghost k) i).trans
      (supportedAssignmentScale_variance x₀ r h c w N ja k.val (x i.val)).symm)
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).1)
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).2.1)
  simpa only [normalizedRoughChart_local x₀ ℓ r h hr.ne', supportedAssignmentScale_rough, hamp] using he

end CausalLowerbound.PartC

import CausalLowerbound.PartC.OutcomePatternContinuity
import CausalLowerbound.PartC.CubeGhostIntegrability
import CausalLowerbound.PartC.PhysicalCompletedOutcomeAll
import CausalLowerbound.PartC.UntaperedGhostMatching

/-! Integrate the exact cubic matching identity over all actual ghost
cubes. Continuity proves integrability; one common resampled sign field
is kept outside the entire product of carrier integrals. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative MvPolynomial RoughOutcome
variable {d I V K G : Type*} [Fintype d] [DecidableEq d]
  [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
  [Fintype K] [DecidableEq K] [Fintype G]

theorem partialPhysicalOutcomeFunctional_integrable
    (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ) (hc : 0 < c)
    (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (p : MvPolynomial V ℝ) :
    Integrable (fun g => partialPhysicalOutcomeFunctional x₀ ℓ r h k c w N B e u a ζ g p)
      (Measure.pi (fun _ : G => cubeMeasure d)) :=
  continuous_integrable_cubeSites _
    (partialPhysicalOutcomeFunctional_continuous x₀ ℓ r h k c w N hc B e u a ζ p)

theorem physical_completed_outcome_ghost_matching
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N a jb t : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hc : 0 < c)
    (hw : 0 < w) (hw1 : w ≤ 1) (hN : N ≠ 0)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (x : I → d → ℝ) (R T smooth : I → ℝ)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    let u₀ := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
      carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
    let z₀ := fun (ζ : activeBlocks (d := d) ℓ h → Bool) (k : S)
      (i : {i // x i ∈ carrierBox x₀ r k.val}) => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (u₀ k i)
    let p := fun (ζ : activeBlocks (d := d) ℓ h → Bool) =>
      ∏ i, outcomeTaylorPolynomial (R i) (T i) 1 jb
        (physicalRoughCorrection x₀ ℓ h (a * t) (x i)) (smooth i)
        (physicalRoughField x₀ ℓ h ζ (x i))
        (∑ k : S, C ((a * linearPartition (localCoordinate x₀ r k.val (x i))) * (t * N)) *
          X (k, retainedObservationSlot Q hQ x₀ r k.val x (e k) i))
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      ∫ ghost : ∀ k, G k → d → ℝ, blockPolynomialFunctional
        (fun k => partialPhysicalOutcomeFunctional x₀ ℓ r h k.val c w N (B k) (e k) (u₀ k) (z₀ ζ k) η (ghost k))
        (p ζ) ∂Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      (∏ k, ∫ ghost : G k → d → ℝ,
        partialPhysicalCarrierValue x₀ ℓ r h k.val c w N (B k) (e k) (u₀ k) (z₀ ζ k) η ghost
          ∂Measure.pi (fun _ : G k => cubeMeasure d)) *
        ∏ i, (likelihood (R i) (T i) jb (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
          (smooth i) (physicalRoughField x₀ ℓ h ζ (x i)) +
            realField (R i) (T i) (smooth i) (targetField x₀ h (a * t * jb) (x i)))) ζ) := by
  dsimp only
  let μ := fun k : S => Measure.pi (fun _ : G k => cubeMeasure d)
  let u₀ := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
    carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
  let z₀ := fun (ζ : activeBlocks (d := d) ℓ h → Bool) (k : S)
    (i : {i // x i ∈ carrierBox x₀ r k.val}) => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (u₀ k i)
  let p := fun (ζ : activeBlocks (d := d) ℓ h → Bool) =>
    ∏ i, outcomeTaylorPolynomial (R i) (T i) 1 jb
      (physicalRoughCorrection x₀ ℓ h (a * t) (x i)) (smooth i)
      (physicalRoughField x₀ ℓ h ζ (x i))
      (∑ k : S, C ((a * linearPartition (localCoordinate x₀ r k.val (x i))) * (t * N)) *
        X (k, retainedObservationSlot Q hQ x₀ r k.val x (e k) i))
  let L := fun ζ η (k : S) => partialPhysicalOutcomeFunctional x₀ ℓ r h k.val c w N (B k) (e k) (u₀ k) (z₀ ζ k) η
  let W := fun ζ η (k : S) => partialPhysicalCarrierValue x₀ ℓ r h k.val c w N (B k) (e k) (u₀ k) (z₀ ζ k) η
  let cells := fun ζ => ∏ i, (likelihood (R i) (T i) jb (physicalRoughCorrection x₀ ℓ h (a * t) (x i))
    (smooth i) (physicalRoughField x₀ ℓ h ζ (x i)) +
      realField (R i) (T i) (smooth i) (targetField x₀ h (a * t * jb) (x i)))
  let f := fun ζ η (ghost : ∀ k, G k → d → ℝ) => blockPolynomialFunctional (fun k => L ζ η k (ghost k)) (p ζ)
  let g := fun ζ η (ghost : ∀ k, G k → d → ℝ) => (∏ k, W ζ η k (ghost k)) * cells ζ
  have hf (ζ η : activeBlocks (d := d) ℓ h → Bool) : Integrable (f ζ η) (Measure.pi μ) := by
    apply continuous_integrable_cubeBlocks G
    apply continuous_blockPolynomialFunctional
    intro k q
    exact (partialPhysicalOutcomeFunctional_continuous x₀ ℓ r h k.val c w N hc
      (B k) (e k) (u₀ k) (z₀ ζ k) η q).comp (continuous_apply k)
  have hg (ζ η : activeBlocks (d := d) ℓ h → Bool) : Integrable (g ζ η) (Measure.pi μ) := by
    apply continuous_integrable_cubeBlocks G
    apply Continuous.mul _ continuous_const
    apply continuous_finset_prod
    intro k _
    exact (partialPhysicalCarrierValue_continuous x₀ ℓ r h k.val c w N hc
      (B k) (e k) (u₀ k) (z₀ ζ k) η).comp (continuous_apply k)
  have he (ghost : ∀ k, G k → d → ℝ) :
      independentSigns.expect (fun ζ => Walsh.resampleAverage
        (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η => f ζ η ghost) ζ) =
      independentSigns.expect (fun ζ => Walsh.resampleAverage
        (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η => g ζ η ghost) ζ) :=
    physical_completed_outcome_matching Q hQ S x₀ ℓ r h c w N a jb t hℓ hr hh hw hw1 hN hm
      x R T smooth hsep hcover htr B G e ghost
  have hint := integrated_resampled_matching
    (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (Measure.pi μ) f g hf hg he
  have hgint (ζ η : activeBlocks (d := d) ℓ h → Bool) :
      (∫ ghost, g ζ η ghost ∂Measure.pi μ) = (∏ k, ∫ ghost, W ζ η k ghost ∂μ k) * cells ζ := by
    change (∫ ghost : ∀ k, G k → d → ℝ, (∏ k, W ζ η k (ghost k)) * cells ζ ∂Measure.pi μ) = _
    rw [integral_mul_const]
    exact congrArg (fun z : ℝ => z * cells ζ)
      (@integral_fintype_prod_eq_prod ℝ inferInstance S inferInstance (fun k => G k → d → ℝ)
        (fun k => W ζ η k) (fun k => ⟨μ k⟩) (fun k => inferInstanceAs (SigmaFinite (μ k))))
  simp_rw [hgint] at hint
  exact hint

end CausalLowerbound.PartC

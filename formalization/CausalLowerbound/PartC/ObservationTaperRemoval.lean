import CausalLowerbound.PartC.CrossBlockTaperRemoval
import CausalLowerbound.PartC.ObservationPatternResampling

/-! The taper-removal estimate for each actual nonempty observation
term. The baseline coefficient and all binary-cell factors are retained;
the bound has the physical shift-times-rough factor required by the rates. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def propensityObservationUntaperedGhostProduct
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c w N ja : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) (s : I → Option S)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) : ℝ :=
  ∏ k : S, ghostPatternIntegral x₀ ℓ r h k.val c w N ja (B k) (e k)
    (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
    (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
      (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η
    ((observationChoiceSet s k).image (retainedObservationSlot Q hQ x₀ r k.val x (e k))) (fun _ => 1)

theorem propensity_observation_taper_removal_bound
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ ja b t τ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hja : 0 ≤ ja) (hsmall : ja * (1 + N₀) ≤ 1) (hb : 0 ≤ b) (ht : 0 ≤ t) (hbtja : b * t ≤ ja)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (hB : ∀ k, ‖B k‖ ≤ 2) (hreflect : ∀ k, reflection (B k) = B k)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q))
    (s : I → Option S) (hs : 0 < choiceDegree s) (T : Finset (activeBlocks (d := d) ℓ h)) :
    let F := propensityObservationGhostProduct Q hQ S x₀ ℓ r h c w N ja τ B x G e s
    let W := propensityObservationUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N ja B x G e s
    let C := 1 + N₀ / c + 1 / (c * N₀)
    let cost := fun k => (2 * C ^ Q) * completedGhostTaperDefect Q (e k) τ
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
    |independentSigns.expect (fun ζ =>
      propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s *
        Walsh.resampleAverage T (fun η => F ζ η - W ζ η) ζ)| ≤
      (b * |propensityChoiceNormalizedCoefficient Q ρ S x₀ r b x y ξ s|) *
        (((2 * C ^ Q) ^ Fintype.card S * ∑ k, cost k) * (2 : ℝ) ^ Fintype.card I *
          ((Fintype.card I : ℝ) + 1) * (t * (ja * (1 + N₀)))) := by
  dsimp only
  let a := propensityChoiceNormalizedCoefficient Q ρ S x₀ r b x y ξ s
  let F := propensityObservationGhostProduct Q hQ S x₀ ℓ r h c w N ja τ B x G e s
  let W := propensityObservationUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N ja B x G e s
  have he (ζ : activeBlocks (d := d) ℓ h → Bool) :
      propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s *
        Walsh.resampleAverage T (fun η => F ζ η - W ζ η) ζ =
      a * ((b * t) ^ choiceDegree s * Walsh.resampleAverage T (fun η => F ζ η - W ζ η) ζ *
        ∏ i, (1 + sign (y i).1 * ja * physicalRoughField x₀ ℓ h ζ (x i))) := by
    rw [propensityObservationCoefficient_false_normalized]
    dsimp only [a]
    ring
  change |independentSigns.expect (fun ζ =>
    propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s *
      Walsh.resampleAverage T (fun η => F ζ η - W ζ η) ζ)| ≤ (b * |a|) * _
  rw [FiniteLaw.expect_congr _ he, FiniteLaw.expect_mul, abs_mul, amplitude_shift_factor]
  by_cases ha : a = 0
  · simp only [ha, abs_zero, zero_mul, le_refl]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
  let Δ := fun (i : I) (k : S) => (1 / 4) * sign (y i).2 *
    linearPartition (localCoordinate x₀ r k.val (x i))
  have hd : (∏ i : ShiftPositions s, Δ i.val (choiceSite s i)) ≠ 0 := (mul_ne_zero_iff.mp ha).2
  have hmem (k : S) (i : I) (hi : Δ i k ≠ 0) : x i ∈ carrierBox x₀ r k.val := by
    apply linearPartition_nonzero_mem_carrierBox
    intro hz
    exact hi (by simp only [Δ, hz, mul_zero])
  let slot := fun k : S => retainedObservationSlot Q hQ x₀ r k.val x (e k)
  let A := fun k : S => (observationChoiceSet s k).image (slot k)
  have hslot (k : S) (i j : I) (hi : Δ i k ≠ 0) (hj : Δ j k ≠ 0)
      (heq : slot k i = slot k j) : i = j :=
    retainedObservationSlot_injective_on_incident Q hQ x₀ r k.val x (e k) i j (hmem k i hi) (hmem k j hj) heq
  have hcard : (∑ k, (A k).card) = choiceDegree s := by
    simp only [A, observationChoiceSet_image_card Δ slot hslot s hd, observationChoiceSet_sum_card]
  have hb := physical_ghost_taper_shift_bound Q x₀ ℓ r h (fun k : S => k.val)
    c w N N₀ ja τ (b * t) hc hN₀ hN hm hrough hja hsmall (mul_nonneg hb ht) hbtja
    (fun k : S => {i // x i ∈ carrierBox x₀ r k.val}) G e
    (fun k i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) A (by omega)
    B hB hreflect T x (fun i => sign (y i).1) (fun i => (abs_sign _).le)
  simpa only [hcard, F, W, propensityObservationGhostProduct, propensityObservationUntaperedGhostProduct,
    A, slot] using hb

end CausalLowerbound.PartC

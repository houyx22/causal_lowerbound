import CausalLowerbound.PartC.OutcomeObservationErrors
import CausalLowerbound.PartC.CubicPatternBounds

/-! A bound for every actual nonconstant cubic observation term, including
collision and transition configurations. Simultaneous parity preserves
the full physical shift times the rough amplitude. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem outcome_observation_pattern_crude_bound
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ jb shift τ : ℝ) (hℓ : 0 < ℓ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1) (hshift : 0 ≤ shift) (hsjb : shift ≤ jb)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (hB : ∀ k, ‖B k‖ ≤ 2) (hreflect : ∀ k, reflection (B k) = B k)
    (x : I → d → ℝ) (y : I → Bool × Bool) (smooth : I → ℝ) (hsmooth : ∀ i, |smooth i| ≤ 1)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (s : I → CubicObservationChoice S) (hs : s ≠ cubicZeroChoice) :
    |independentSigns.expect (fun ζ => outcomeObservationChoiceCoefficient S x₀ ℓ r h jb shift x y smooth s ζ *
      outcomeObservationPatternProduct true Q hQ S x₀ ℓ r h c w N τ B x G e s ζ ζ)| ≤
      ((1 / 4 : ℝ) ^ Fintype.card I *
        |cubicObservationChoiceWeight (fun i k => linearPartition (localCoordinate x₀ r k.val (x i))) s|) *
        ((2 * ((1 + N₀ / c + 1 / N₀ ^ 2) ^ 4) ^ Q) ^ Fintype.card S *
          outcomeObservationScalarScale (Fintype.card I) N₀ jb shift) := by
  let C := 1 + N₀ / c + 1 / N₀ ^ 2
  let M := 2 * (C ^ 4) ^ Q
  let F := outcomeObservationPatternProduct true Q hQ S x₀ ℓ r h c w N τ B x G e s
  let δ := fun (i : I) (k : S) => linearPartition (localCoordinate x₀ r k.val (x i))
  let slot := fun k : S => retainedObservationSlot Q hQ x₀ r k.val x (e k)
  let Z := fun (ζ : activeBlocks (d := d) ℓ h → Bool) (k : S) (f : Degree (Fin Q) 3) =>
    physicalGhostOutcomePatternWeight Q x₀ ℓ r h k.val c w N τ (B k) (e k)
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) ζ ζ f
  let g := fun (i : I) ζ => outcomeTaylorCoefficient (sign (y i).1) (sign (y i).2) 1 jb
    (physicalRoughCorrection x₀ ℓ h shift (x i)) (smooth i) (physicalRoughField x₀ ℓ h ζ (x i)) (s i).1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hZ ζ k f : |Z ζ k f| ≤ M := by
    apply (physicalGhostOutcomePatternWeight_bound Q x₀ ℓ r h k.val c w N N₀ τ hc hN₀ hN
      hm hrough (B k) (e k) _ ζ ζ f).trans
    simpa only [M, C, mul_comm] using mul_le_mul_of_nonneg_left (hB k)
      (pow_nonneg (pow_nonneg hC 4) Q)
  have hF ζ : |F ζ ζ| ≤ M ^ Fintype.card S := by
    simpa only [F, outcomeObservationPatternProduct, outcomeObservationPatternWeight, if_pos rfl, if_true, Z, slot] using
      cubicObservationPatternProduct_bound (Z ζ) M hM (hZ ζ) slot s
  have hparity ζ : F (Walsh.flip ζ) (Walsh.flip ζ) = (-1) ^ cubicObservationChoiceDegree s * F ζ ζ := by
    have hp ζ k f : Z (Walsh.flip ζ) k f = (-1) ^ degreeSize f * Z ζ k f :=
      physicalGhostOutcomePatternWeight_parity Q x₀ ℓ r h k.val c w N τ (B k) (hreflect k) (e k) _ ζ ζ f
    simpa only [F, outcomeObservationPatternProduct, outcomeObservationPatternWeight, if_pos rfl, if_true, Z, slot] using
      cubicObservationPatternProduct_parity Z hp slot s ζ
  have he ζ : outcomeObservationChoiceCoefficient S x₀ ℓ r h jb shift x y smooth s ζ * F ζ ζ =
      ((1 / 4 : ℝ) ^ Fintype.card I * cubicObservationChoiceWeight δ s) *
        (shift ^ cubicObservationChoiceDegree s * F ζ ζ * ∏ i, g i ζ) := by
    unfold outcomeObservationChoiceCoefficient
    dsimp only [δ, g]
    ring
  change |independentSigns.expect (fun ζ =>
    outcomeObservationChoiceCoefficient S x₀ ℓ r h jb shift x y smooth s ζ * F ζ ζ)| ≤ _
  rw [FiniteLaw.expect_congr _ he, FiniteLaw.expect_mul, abs_mul, abs_mul,
    abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) _)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (abs_nonneg _))
  have hg i ζ := physicalOutcomeTaylorCoefficient_bounds x₀ ℓ h N₀ jb shift hℓ hN₀
    hrough hjb hsmall hshift hsjb (x i) (y i) (smooth i) (hsmooth i) ζ (s i).1
  have hb i : |outcomeTaylorBase (sign (y i).1) (smooth i) (s i).1| ≤ 12 :=
    (outcomeTaylorBase_bound _ _ (abs_sign _).le (hsmooth i) _).trans (by norm_num)
  have hresult := parity_weighted_scalar_product_shift_bound (cubicObservationChoiceDegree s)
    (cubicObservationChoiceDegree_pos_of_ne_zero s hs) (fun ζ => F ζ ζ) hparity g
    (fun i => outcomeTaylorBase (sign (y i).1) (smooth i) (s i).1)
    (M ^ Fintype.card S) 12 shift (jb * (1 + N₀)) (pow_nonneg hM _) (by norm_num)
    hshift (by positivity) hsmall (hsjb.trans (le_mul_of_one_le_right hjb (by linarith)))
    hF (fun i ζ => (hg i ζ).1) hb (fun i ζ => (hg i ζ).2)
  simpa only [outcomeObservationScalarScale, M, C, mul_assoc] using hresult

theorem outcome_observation_baseline_bound
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c w N N₀ τ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (hB : ∀ k, ‖B k‖ ≤ 2)
    (x : I → d → ℝ) (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) :
    |∏ k, outcomeObservationPatternWeight false Q S x₀ ℓ r h c w N τ B x G e ζ η k 0| ≤
      (2 * ((1 + N₀ / c + 1 / N₀ ^ 2) ^ 4) ^ Q) ^ Fintype.card S := by
  let C := 1 + N₀ / c + 1 / N₀ ^ 2
  let M := 2 * (C ^ 4) ^ Q
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply bounded_scalar_product _ M (by dsimp [M]; positivity)
  intro k
  rw [← outcomeObservationPatternWeight_zero true Q S x₀ ℓ r h c w N τ B x G e ζ η k]
  change |physicalGhostOutcomePatternWeight Q x₀ ℓ r h k.val c w N τ (B k) (e k)
    (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) ζ η 0| ≤ M
  apply (physicalGhostOutcomePatternWeight_bound Q x₀ ℓ r h k.val c w N N₀ τ hc hN₀ hN
    hm hrough (B k) (e k) _ ζ η 0).trans
  simpa only [M, C, mul_comm] using mul_le_mul_of_nonneg_left (hB k) (pow_nonneg (pow_nonneg hC 4) Q)

end CausalLowerbound.PartC

import CausalLowerbound.PartC.OutcomeObservationResampling
import CausalLowerbound.PartC.CrossBlockOutcomeTaperRemoval

/-! Remove the complete-graph taper from an actual nonzero cubic
observation term. Its cost keeps the physical shift times the rough
amplitude after averaging the shared signs. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem physicalOutcomeTaylorCoefficient_bounds
    (x₀ : d → ℝ) (ℓ h N₀ jb shift : ℝ) (hℓ : 0 < ℓ) (hN₀ : 0 < N₀)
    (hfield : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1) (hshift : 0 ≤ shift) (hsjb : shift ≤ jb)
    (x : d → ℝ) (y : Bool × Bool) (smooth : ℝ) (hsmooth : |smooth| ≤ 1)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (f : Fin 4) :
    |outcomeTaylorCoefficient (sign y.1) (sign y.2) 1 jb
      (physicalRoughCorrection x₀ ℓ h shift x) smooth (physicalRoughField x₀ ℓ h ζ x) f| ≤ 12 ∧
    |outcomeTaylorCoefficient (sign y.1) (sign y.2) 1 jb
      (physicalRoughCorrection x₀ ℓ h shift x) smooth (physicalRoughField x₀ ℓ h ζ x) f -
        outcomeTaylorBase (sign y.1) smooth f| ≤ 12 * (jb * (1 + N₀)) := by
  have hjb1 : jb ≤ 1 := (le_mul_of_one_le_right hjb (by linarith : 1 ≤ 1 + N₀)).trans hsmall
  have hη : |physicalRoughCorrection x₀ ℓ h shift x| ≤ 3 := by
    have hh := physicalRoughCorrection_bounds x₀ ℓ h shift hℓ x
    rw [abs_of_nonneg hh.1]
    exact hh.2.trans (by nlinarith [pow_le_one₀ hshift (hsjb.trans hjb1) (n := 2)])
  have hb : |physicalRoughField x₀ ℓ h ζ x| ≤ N₀ := by
    rw [← physicalRoughWalsh_evaluate]
    exact (Walsh.evaluate_bound ζ _).trans (hfield _)
  have hr : |jb * physicalRoughField x₀ ℓ h ζ x| ≤ jb * (1 + N₀) := by
    rw [abs_mul, abs_of_nonneg hjb]
    exact mul_le_mul_of_nonneg_left (hb.trans (by linarith)) hjb
  exact outcomeTaylorCoefficient_unit_bounds (sign y.1) (sign y.2) jb
    (physicalRoughCorrection x₀ ℓ h shift x) smooth (physicalRoughField x₀ ℓ h ζ x) (jb * (1 + N₀))
    (abs_sign _).le (abs_sign _).le hη hsmooth (by positivity) hsmall hr f

def outcomeObservationChoiceUntaperedGhostProduct
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c w N : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (s : I → CubicObservationChoice S)
    (hs : ∀ v, siteOccurrenceExponent
      (cubicObservationChoiceSlot (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) s) v ≤ 3)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) : ℝ :=
  let slot : S → I → Fin Q := fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)
  let D : Degree (S × Fin Q) 3 := cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs
  ∏ k : S, ghostOutcomePatternIntegral x₀ ℓ r h k.val c w N (B k) (e k)
    (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
    (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
      (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η (fun v => D (k, v)) (fun _ => 1)

theorem outcome_observation_choice_taper_removal_bound
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
    (s : I → CubicObservationChoice S) (hpos : 0 < cubicObservationChoiceDegree s)
    (hs : ∀ v, siteOccurrenceExponent
      (cubicObservationChoiceSlot (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) s) v ≤ 3)
    (T : Finset (activeBlocks (d := d) ℓ h)) :
    let F := outcomeObservationChoiceGhostProduct Q hQ S x₀ ℓ r h c w N τ B x G e s hs
    let W := outcomeObservationChoiceUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N B x G e s hs
    let C := 1 + N₀ / c + 1 / N₀ ^ 2
    |independentSigns.expect (fun ζ => outcomeObservationChoiceCoefficient S x₀ ℓ r h jb shift x y smooth s ζ *
      Walsh.resampleAverage T (fun η => F ζ η - W ζ η) ζ)| ≤
      ((1 / 4 : ℝ) ^ Fintype.card I *
        |cubicObservationChoiceWeight (fun i k => linearPartition (localCoordinate x₀ r k.val (x i))) s|) *
        (((2 * (C ^ 4) ^ Q) ^ Fintype.card S *
          ∑ k, (2 * (C ^ 4) ^ Q) * completedGhostTaperDefect Q (e k) τ
            (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) *
          ((12 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) * 12 + 1)) *
            (shift * (jb * (1 + N₀)))) := by
  dsimp only
  let F := outcomeObservationChoiceGhostProduct Q hQ S x₀ ℓ r h c w N τ B x G e s hs
  let W := outcomeObservationChoiceUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N B x G e s hs
  let δ := fun (i : I) (k : S) => linearPartition (localCoordinate x₀ r k.val (x i))
  let slot := fun k : S => retainedObservationSlot Q hQ x₀ r k.val x (e k)
  let D := fun (k : S) v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v)
  let g := fun (i : I) ζ => outcomeTaylorCoefficient (sign (y i).1) (sign (y i).2) 1 jb
    (physicalRoughCorrection x₀ ℓ h shift (x i)) (smooth i) (physicalRoughField x₀ ℓ h ζ (x i)) (s i).1
  have he (ζ : activeBlocks (d := d) ℓ h → Bool) :
      outcomeObservationChoiceCoefficient S x₀ ℓ r h jb shift x y smooth s ζ *
        Walsh.resampleAverage T (fun η => F ζ η - W ζ η) ζ =
      ((1 / 4 : ℝ) ^ Fintype.card I * cubicObservationChoiceWeight δ s) *
        (shift ^ cubicObservationChoiceDegree s *
          Walsh.resampleAverage T (fun η => F ζ η - W ζ η) ζ * ∏ i, g i ζ) := by
    unfold outcomeObservationChoiceCoefficient
    dsimp only [δ, g]
    ring
  rw [FiniteLaw.expect_congr _ he, FiniteLaw.expect_mul, abs_mul, abs_mul,
    abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) _)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (abs_nonneg _))
  have hdeg : (∑ k, degreeSize (D k)) = cubicObservationChoiceDegree s :=
    cubicObservationChoice_degree_sum slot s hs
  have hg (i : I) ζ := physicalOutcomeTaylorCoefficient_bounds x₀ ℓ h N₀ jb shift hℓ hN₀
    hrough hjb hsmall hshift hsjb (x i) (y i) (smooth i) (hsmooth i) ζ (s i).1
  have hb (i : I) : |outcomeTaylorBase (sign (y i).1) (smooth i) (s i).1| ≤ 12 :=
    (outcomeTaylorBase_bound _ _ (abs_sign _).le (hsmooth i) _).trans (by norm_num)
  have hh := physical_ghost_outcome_taper_scalar_bound Q x₀ ℓ r h (fun k : S => k.val)
    c w N N₀ τ shift (jb * (1 + N₀)) 12 hc hN₀ hN hm hrough hshift (by positivity) hsmall
    (hsjb.trans (le_mul_of_one_le_right hjb (by linarith))) (by norm_num)
    (fun k : S => {i // x i ∈ carrierBox x₀ r k.val}) G e
    (fun k i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) D (by rwa [hdeg])
    B hB hreflect T g (fun i => outcomeTaylorBase (sign (y i).1) (smooth i) (s i).1)
    (fun i ζ => (hg i ζ).1) hb (fun i ζ => (hg i ζ).2)
  simpa only [hdeg, F, W, g, outcomeObservationChoiceGhostProduct,
    outcomeObservationChoiceUntaperedGhostProduct, D, slot] using hh

end CausalLowerbound.PartC

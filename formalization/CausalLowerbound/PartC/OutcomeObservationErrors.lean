import CausalLowerbound.PartC.OutcomeObservationFactors
import CausalLowerbound.PartC.OutcomeSignRestoration

/-! Explicit common error budgets for all cubic observation choices.
Both pattern errors retain the physical shift times the rough amplitude. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def outcomeObservationSignCost
    (Q : ℕ) (S : Finset (d → ℤ)) (ℓ r h c N N₀ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (G : S → Type*) [∀ k, Fintype (G k)] (T : Finset (activeBlocks (d := d) ℓ h)) : ℝ :=
  let C := 1 + N₀ / c + 1 / N₀ ^ 2
  (2 * (C ^ 4) ^ Q) ^ Fintype.card S * ∑ k, ∑ j ∈ T,
    (C ^ 4) ^ Q * (2 * ‖symbolPart j (B k)‖ + (3 * ‖B k - unit‖) *
      ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))

def outcomeObservationTaperCost
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r c N₀ τ : ℝ)
    (x : I → d → ℝ) (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) : ℝ :=
  let C := 1 + N₀ / c + 1 / N₀ ^ 2
  (2 * (C ^ 4) ^ Q) ^ Fintype.card S * ∑ k, (2 * (C ^ 4) ^ Q) *
    completedGhostTaperDefect Q (e k) τ
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))

def outcomeObservationScalarScale (q : ℕ) (N₀ jb shift : ℝ) : ℝ :=
  (12 : ℝ) ^ q * ((q : ℝ) * 12 + 1) * (shift * (jb * (1 + N₀)))

theorem outcomeObservationSignCost_nonneg
    (Q : ℕ) (S : Finset (d → ℤ)) (ℓ r h c N N₀ : ℝ)
    (hℓ : 0 ≤ ℓ) (hr : 0 ≤ r) (hc : 0 ≤ c) (hN : 0 ≤ N)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (G : S → Type*) [∀ k, Fintype (G k)] (T : Finset (activeBlocks (d := d) ℓ h)) :
    0 ≤ outcomeObservationSignCost Q S ℓ r h c N N₀ B G T := by
  unfold outcomeObservationSignCost
  positivity

theorem outcomeObservationTaperCost_nonneg
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r c N₀ τ : ℝ)
    (x : I → d → ℝ) (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    0 ≤ outcomeObservationTaperCost Q S x₀ r c N₀ τ x G e := by
  unfold outcomeObservationTaperCost
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (by positivity) (completedGhostTaperDefect_bounds Q (e k) τ _).1

theorem outcomeObservationScalarScale_nonneg (q : ℕ) (N₀ jb shift : ℝ)
    (hN₀ : 0 ≤ N₀) (hjb : 0 ≤ jb) (hshift : 0 ≤ shift) :
    0 ≤ outcomeObservationScalarScale q N₀ jb shift := by
  unfold outcomeObservationScalarScale
  positivity

theorem outcome_observation_pattern_resampling_bound
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (c w N N₀ jb shift τ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1) (hshift : 0 ≤ shift) (hsjb : shift ≤ jb)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (hB : ∀ k, ‖B k‖ ≤ 2) (hreflect : ∀ k, reflection (B k) = B k)
    (x : I → d → ℝ) (y : I → Bool × Bool) (smooth : I → ℝ) (hsmooth : ∀ i, |smooth i| ≤ 1)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (s : I → CubicObservationChoice S) (hs : s ≠ cubicZeroChoice)
    (T : Finset (activeBlocks (d := d) ℓ h)) :
    let F := outcomeObservationPatternProduct true Q hQ S x₀ ℓ r h c w N τ B x G e s
    |independentSigns.expect (fun ζ => outcomeObservationChoiceCoefficient S x₀ ℓ r h jb shift x y smooth s ζ *
      (F ζ ζ - Walsh.resampleAverage T (F ζ) ζ))| ≤
      ((1 / 4 : ℝ) ^ Fintype.card I *
        |cubicObservationChoiceWeight (fun i k => linearPartition (localCoordinate x₀ r k.val (x i))) s|) *
        (outcomeObservationSignCost Q S ℓ r h c N N₀ B G T *
          outcomeObservationScalarScale (Fintype.card I) N₀ jb shift) := by
  dsimp only
  by_cases hv : ∀ v, siteOccurrenceExponent
      (cubicObservationChoiceSlot (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) s) v ≤ 3
  · have hF : outcomeObservationPatternProduct true Q hQ S x₀ ℓ r h c w N τ B x G e s =
        outcomeObservationChoiceGhostProduct Q hQ S x₀ ℓ r h c w N τ B x G e s hv := by
      funext ζ η
      exact (outcomeObservationPatternProduct_valid Q hQ S x₀ ℓ r h c w N τ B x G e s hv ζ η).1
    rw [hF]
    have hb := outcome_observation_choice_resampling_bound Q hQ S x₀ ℓ r h hℓ hr c w N N₀ jb shift τ hc hN₀ hN
      hm hrough hjb hsmall hshift hsjb B hB hreflect x y smooth hsmooth G e s
        (cubicObservationChoiceDegree_pos_of_ne_zero s hs) hv T
    dsimp only at hb
    apply hb.trans_eq
    simp only [outcomeObservationSignCost, outcomeObservationScalarScale, mul_assoc]
  · have hF : outcomeObservationPatternProduct true Q hQ S x₀ ℓ r h c w N τ B x G e s =
        (fun _ _ => 0) := by
      funext ζ η
      exact outcomeObservationPatternProduct_invalid true Q hQ S x₀ ℓ r h c w N τ B x G e s hv ζ η
    rw [hF]
    simp only [Walsh.resampleAverage, FiniteLaw.expect_const, sub_self, mul_zero, abs_zero]
    have hsign := outcomeObservationSignCost_nonneg Q S ℓ r h c N N₀ hℓ.le hr.le hc.le
      ((div_pos hN₀ hc).trans_le hN).le B G T
    have hscale := outcomeObservationScalarScale_nonneg (Fintype.card I) N₀ jb shift hN₀.le hjb hshift
    exact mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) (mul_nonneg hsign hscale)

theorem outcome_observation_pattern_taper_bound
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
    (s : I → CubicObservationChoice S) (hs : s ≠ cubicZeroChoice)
    (T : Finset (activeBlocks (d := d) ℓ h)) :
    let F := outcomeObservationPatternProduct true Q hQ S x₀ ℓ r h c w N τ B x G e s
    let W := outcomeObservationPatternProduct false Q hQ S x₀ ℓ r h c w N τ B x G e s
    |independentSigns.expect (fun ζ => outcomeObservationChoiceCoefficient S x₀ ℓ r h jb shift x y smooth s ζ *
      Walsh.resampleAverage T (fun η => F ζ η - W ζ η) ζ)| ≤
      ((1 / 4 : ℝ) ^ Fintype.card I *
        |cubicObservationChoiceWeight (fun i k => linearPartition (localCoordinate x₀ r k.val (x i))) s|) *
        (outcomeObservationTaperCost Q S x₀ r c N₀ τ x G e *
          outcomeObservationScalarScale (Fintype.card I) N₀ jb shift) := by
  dsimp only
  by_cases hv : ∀ v, siteOccurrenceExponent
      (cubicObservationChoiceSlot (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) s) v ≤ 3
  · have hF : outcomeObservationPatternProduct true Q hQ S x₀ ℓ r h c w N τ B x G e s =
        outcomeObservationChoiceGhostProduct Q hQ S x₀ ℓ r h c w N τ B x G e s hv := by
      funext ζ η
      exact (outcomeObservationPatternProduct_valid Q hQ S x₀ ℓ r h c w N τ B x G e s hv ζ η).1
    have hW : outcomeObservationPatternProduct false Q hQ S x₀ ℓ r h c w N τ B x G e s =
        outcomeObservationChoiceUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N B x G e s hv := by
      funext ζ η
      exact (outcomeObservationPatternProduct_valid Q hQ S x₀ ℓ r h c w N τ B x G e s hv ζ η).2
    rw [hF, hW]
    have hb := outcome_observation_choice_taper_removal_bound Q hQ S x₀ ℓ r h c w N N₀ jb shift τ hℓ hc hN₀ hN
      hm hrough hjb hsmall hshift hsjb B hB hreflect x y smooth hsmooth G e s
        (cubicObservationChoiceDegree_pos_of_ne_zero s hs) hv T
    dsimp only at hb
    apply hb.trans_eq
    simp only [outcomeObservationTaperCost, outcomeObservationScalarScale, mul_assoc]
  · simp_rw [outcomeObservationPatternProduct_invalid true Q hQ S x₀ ℓ r h c w N τ B x G e s hv,
      outcomeObservationPatternProduct_invalid false Q hQ S x₀ ℓ r h c w N τ B x G e s hv]
    simp only [sub_self, Walsh.resampleAverage, FiniteLaw.expect_const, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
      (mul_nonneg (outcomeObservationTaperCost_nonneg Q S x₀ r c N₀ τ x G e)
        (outcomeObservationScalarScale_nonneg (Fintype.card I) N₀ jb shift hN₀.le hjb hshift))

end CausalLowerbound.PartC

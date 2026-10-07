import CausalLowerbound.PartC.CubicObservationNormalization
import CausalLowerbound.PartC.CrossBlockGhostOutcomePatterns
import CausalLowerbound.PartC.RetainedObservationSlots

/-! Shared-sign resampling for an actual nonempty cubic observation term.
Its physical partition coefficients force every selected slot to be
retained, and the total occurrence degree supplies exactly the shift power. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def outcomeObservationChoiceCoefficient (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h jb shift : ℝ) (x : I → d → ℝ) (y : I → Bool × Bool) (smooth : I → ℝ)
    (s : I → CubicObservationChoice S) (ζ : activeBlocks (d := d) ℓ h → Bool) : ℝ :=
  (1 / 4 : ℝ) ^ Fintype.card I * shift ^ cubicObservationChoiceDegree s *
    (∏ i, outcomeTaylorCoefficient (sign (y i).1) (sign (y i).2) 1 jb
      (physicalRoughCorrection x₀ ℓ h shift (x i)) (smooth i) (physicalRoughField x₀ ℓ h ζ (x i)) (s i).1) *
      cubicObservationChoiceWeight (fun i k => linearPartition (localCoordinate x₀ r k.val (x i))) s

def outcomeObservationChoiceGhostProduct
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c w N τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (s : I → CubicObservationChoice S)
    (hs : ∀ v, siteOccurrenceExponent
      (cubicObservationChoiceSlot (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) s) v ≤ 3)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) : ℝ :=
  let slot : S → I → Fin Q := fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)
  let D : Degree (S × Fin Q) 3 := cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs
  ∏ k : S, physicalGhostOutcomePatternWeight Q x₀ ℓ r h k.val c w N τ (B k) (e k)
    (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) ζ η
    (fun v => D (k, v))

theorem outcome_observation_choice_resampling_bound
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
    (s : I → CubicObservationChoice S) (hpos : 0 < cubicObservationChoiceDegree s)
    (hs : ∀ v, siteOccurrenceExponent
      (cubicObservationChoiceSlot (fun k => retainedObservationSlot Q hQ x₀ r k.val x (e k)) s) v ≤ 3)
    (T : Finset (activeBlocks (d := d) ℓ h)) :
    let F := outcomeObservationChoiceGhostProduct Q hQ S x₀ ℓ r h c w N τ B x G e s hs
    let C := 1 + N₀ / c + 1 / N₀ ^ 2
    let cost := fun k j => (C ^ 4) ^ Q * (2 * ‖symbolPart j (B k)‖ + (3 * ‖B k - unit‖) *
      ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))
    |independentSigns.expect (fun ζ => outcomeObservationChoiceCoefficient S x₀ ℓ r h jb shift x y smooth s ζ *
      (F ζ ζ - Walsh.resampleAverage T (F ζ) ζ))| ≤
      ((1 / 4 : ℝ) ^ Fintype.card I *
        |cubicObservationChoiceWeight (fun i k => linearPartition (localCoordinate x₀ r k.val (x i))) s|) *
        (((2 * (C ^ 4) ^ Q) ^ Fintype.card S * ∑ k, ∑ j ∈ T, cost k j) *
          ((12 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) * 12 + 1)) *
            (shift * (jb * (1 + N₀)))) := by
  dsimp only
  let F := outcomeObservationChoiceGhostProduct Q hQ S x₀ ℓ r h c w N τ B x G e s hs
  let δ := fun (i : I) (k : S) => linearPartition (localCoordinate x₀ r k.val (x i))
  let slot := fun k : S => retainedObservationSlot Q hQ x₀ r k.val x (e k)
  let D := fun (k : S) v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v)
  have he (ζ : activeBlocks (d := d) ℓ h → Bool) :
      outcomeObservationChoiceCoefficient S x₀ ℓ r h jb shift x y smooth s ζ *
        (F ζ ζ - Walsh.resampleAverage T (F ζ) ζ) =
      ((1 / 4 : ℝ) ^ Fintype.card I * cubicObservationChoiceWeight δ s) *
        (shift ^ cubicObservationChoiceDegree s * (F ζ ζ - Walsh.resampleAverage T (F ζ) ζ) *
          ∏ i, outcomeTaylorCoefficient (sign (y i).1) (sign (y i).2) 1 jb
            (physicalRoughCorrection x₀ ℓ h shift (x i)) (smooth i)
            (physicalRoughField x₀ ℓ h ζ (x i)) (s i).1) := by
    unfold outcomeObservationChoiceCoefficient
    dsimp only [δ]
    ring
  rw [FiniteLaw.expect_congr _ he, FiniteLaw.expect_mul, abs_mul, abs_mul,
    abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) _)]
  by_cases hδ : cubicObservationChoiceWeight δ s = 0
  · dsimp only [δ] at hδ
    simp only [δ, hδ, abs_zero, mul_zero, zero_mul, le_refl]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (abs_nonneg _))
  have hret (k : S) (v : Fin Q) (hv : D k v ≠ 0) :
      ∃ i : {i // x i ∈ carrierBox x₀ r k.val}, e k (Sum.inl i) = v := by
    apply cubicObservationChoice_supported δ slot
      (fun k v => ∃ i : {i // x i ∈ carrierBox x₀ r k.val}, e k (Sum.inl i) = v) _ s hδ hs k v hv
    intro i k hi
    have hxi := linearPartition_nonzero_mem_carrierBox x₀ r k.val (x i) hi
    exact ⟨⟨i, hxi⟩, (retainedObservationSlot_incident Q hQ x₀ r k.val x (e k) i hxi).symm⟩
  have hdeg : (∑ k, degreeSize (D k)) = cubicObservationChoiceDegree s :=
    cubicObservationChoice_degree_sum slot s hs
  have hjb1 : jb ≤ 1 := (le_mul_of_one_le_right hjb (by linarith : 1 ≤ 1 + N₀)).trans hsmall
  have hη (i : I) : |physicalRoughCorrection x₀ ℓ h shift (x i)| ≤ 3 := by
    have hh := physicalRoughCorrection_bounds x₀ ℓ h shift hℓ (x i)
    rw [abs_of_nonneg hh.1]
    exact hh.2.trans (by nlinarith [pow_le_one₀ hshift (hsjb.trans hjb1) (n := 2)])
  have hb := physical_ghost_outcome_pattern_resampling_bound Q x₀ ℓ r h hℓ hr (fun k : S => k.val)
    c w N N₀ jb τ shift hc hN₀ hN hm hrough hjb hsmall hshift hsjb
    (fun k : S => {i // x i ∈ carrierBox x₀ r k.val}) G e
    (fun k i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) D (by rwa [hdeg]) hret
    B hB hreflect T x (fun i => sign (y i).1) (fun i => sign (y i).2)
    (fun i => physicalRoughCorrection x₀ ℓ h shift (x i)) smooth (fun i => (s i).1)
    (fun i => (abs_sign _).le) (fun i => (abs_sign _).le) hη hsmooth
  simpa only [hdeg, F, outcomeObservationChoiceGhostProduct, D, slot] using hb

end CausalLowerbound.PartC

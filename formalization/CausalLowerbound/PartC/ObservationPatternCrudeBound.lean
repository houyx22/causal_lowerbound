import CausalLowerbound.PartC.ObservationPatternResampling

/-! A uniform nonempty-pattern bound without spatial separation or
assignment-interior assumptions. Simultaneous parity retains t * ja,
including on the bad configurations used in the information bound. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem propensity_observation_pattern_bound
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ ja b t τ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hja : 0 ≤ ja) (hsmall : ja * (1 + N₀) ≤ 1) (hb : 0 ≤ b) (ht : 0 ≤ t) (hbtja : b * t ≤ ja)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (hB : ∀ k, ‖B k‖ ≤ 2) (hreflect : ∀ k, reflection (B k) = B k)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q))
    (s : I → Option S) (hs : 0 < choiceDegree s) :
    let C := 1 + N₀ / c + 1 / (c * N₀)
    |independentSigns.expect (fun ζ =>
      propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s *
        propensityObservationGhostProduct Q hQ S x₀ ℓ r h c w N ja τ B x G e s ζ ζ)| ≤
      (b * |propensityChoiceNormalizedCoefficient Q ρ S x₀ r b x y ξ s|) *
        ((2 * C ^ Q) ^ Fintype.card S * (2 : ℝ) ^ Fintype.card I *
          ((Fintype.card I : ℝ) + 1) * (t * (ja * (1 + N₀)))) := by
  dsimp only
  let a := propensityChoiceNormalizedCoefficient Q ρ S x₀ r b x y ξ s
  let F := propensityObservationGhostProduct Q hQ S x₀ ℓ r h c w N ja τ B x G e s
  have he ζ : propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s * F ζ ζ =
      a * ((b * t) ^ choiceDegree s * F ζ ζ * ∏ i, (1 + sign (y i).1 * ja * physicalRoughField x₀ ℓ h ζ (x i))) := by
    rw [propensityObservationCoefficient_false_normalized]
    dsimp only [a]
    ring
  change |independentSigns.expect (fun ζ =>
    propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s * F ζ ζ)| ≤ (b * |a|) * _
  rw [FiniteLaw.expect_congr _ he, FiniteLaw.expect_mul, abs_mul, amplitude_shift_factor]
  by_cases ha : a = 0
  · simp only [ha, abs_zero, zero_mul, le_refl]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
  let Δ := fun (i : I) (k : S) => (1 / 4) * sign (y i).2 * linearPartition (localCoordinate x₀ r k.val (x i))
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
  let C := 1 + N₀ / c + 1 / (c * N₀)
  let M := 2 * C ^ Q
  let u := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
    carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
  let Z := fun (k : S) ζ η => physicalGhostPatternWeight Q x₀ ℓ r h k.val c w N ja τ (B k) (e k) (u k) ζ η (A k)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hja' : ja ≤ ja * (1 + N₀) := le_mul_of_one_le_right hja (by linarith)
  have hja2 : ja ^ 2 ≤ 1 := pow_le_one₀ hja (hja'.trans hsmall)
  have hZ (k : S) ζ η : |Z k ζ η| ≤ M := by
    apply (physicalGhostPatternWeight_bound Q x₀ ℓ r h k.val c w N N₀ ja τ hc hN₀ hN
      hm hrough hja2 (B k) (e k) (u k) ζ η (A k)).trans
    simpa only [M, mul_comm] using mul_le_mul_of_nonneg_left (hB k) (pow_nonneg hC Q)
  have hp (k : S) ζ η : Z k (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ (A k).card * Z k ζ η :=
    physicalGhostPatternWeight_parity Q x₀ ℓ r h k.val c w N ja τ (B k) (hreflect k) (e k) (u k) ζ η (A k)
  have hparity ζ : F (Walsh.flip ζ) (Walsh.flip ζ) = (-1) ^ choiceDegree s * F ζ ζ := by
    change (∏ k, Z k (Walsh.flip ζ) (Walsh.flip ζ)) = (-1) ^ choiceDegree s * ∏ k, Z k ζ ζ
    simp only [hp, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hcard]
  have hF ζ : |F ζ ζ| ≤ M ^ Fintype.card S := by
    change |∏ k, Z k ζ ζ| ≤ _
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k _ => hZ k ζ ζ)).trans (by simp)
  have hf (i : I) ζ : |sign (y i).1 * ja * physicalRoughField x₀ ℓ h ζ (x i)| ≤ ja * (1 + N₀) := by
    have hx : |physicalRoughField x₀ ℓ h ζ (x i)| ≤ N₀ := by
      rw [← physicalRoughWalsh_evaluate]
      exact (Walsh.evaluate_bound ζ _).trans (hrough _)
    rw [abs_mul, abs_mul, abs_sign, abs_of_nonneg hja, one_mul]
    exact (mul_le_mul_of_nonneg_left hx hja).trans (by nlinarith)
  exact parity_weighted_shift_bound (choiceDegree s) hs (fun ζ => F ζ ζ) hparity
    (fun i ζ => sign (y i).1 * ja * physicalRoughField x₀ ℓ h ζ (x i))
    (M ^ Fintype.card S) (b * t) (ja * (1 + N₀)) (pow_nonneg hM _) (mul_nonneg hb ht) (by positivity)
    hsmall (hbtja.trans hja') hF hf

end CausalLowerbound.PartC

import CausalLowerbound.PartC.OutcomeObservationPatternBounds

/-! A complete outcome comparison on arbitrary configurations. The
constant depends only on finite observation/block counts and fixed carrier
parameters; the error retains the full target amplitude a*t*jb. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def outcomeCrudeConstant (Q q k : ℕ) (c N₀ : ℝ) : ℝ :=
  (2 * ((1 + N₀ / c + 1 / N₀ ^ 2) ^ 4) ^ Q) ^ k *
    ((1 + (k : ℝ) + (k : ℝ) ^ 2 + (k : ℝ) ^ 3) ^ q *
      (12 : ℝ) ^ q * ((q : ℝ) * 12 + 1) * (1 + N₀) + (5 : ℝ) ^ q * q * (3 / 2 : ℝ))

theorem outcomeCrudeConstant_nonneg (Q q k : ℕ) (c N₀ : ℝ) (hN₀ : 0 ≤ N₀) :
    0 ≤ outcomeCrudeConstant Q q k c N₀ := by
  unfold outcomeCrudeConstant
  positivity

theorem physical_outcome_observation_crude_bound
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (U : S → CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h c w N N₀ a jb t τ : ℝ) (hℓ : 0 < ℓ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1) (hshift : 0 ≤ a * t) (hsjb : a * t ≤ jb)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (hB : ∀ k, ‖B k‖ ≤ 2) (hreflect : ∀ k, reflection (B k) = B k)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hsmooth : ∀ i, |a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    |independentSigns.expect (fun ζ =>
        outcomeObservationValue true Q hQ S x₀ ℓ r h c w N jb (a * t) τ B x y
          (fun i => a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i))) G e ζ ζ) -
      independentSigns.expect (fun ζ =>
        (∏ k, outcomeObservationPatternWeight false Q S x₀ ℓ r h c w N τ B x G e ζ ζ k 0) *
          eval (fun ka => U ka.1 ka.2) (mixedOutcomeComponentPolynomial Q true S x₀ ℓ r h a jb t ζ x y))| ≤
      outcomeCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |a * t * jb| := by
  let smooth := fun i => a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i))
  let coeff := fun ζ s => outcomeObservationChoiceCoefficient S x₀ ℓ r h jb (a * t) x y smooth s ζ
  let F := outcomeObservationPatternProduct true Q hQ S x₀ ℓ r h c w N τ B x G e
  let value := fun ζ => outcomeObservationValue true Q hQ S x₀ ℓ r h c w N jb (a * t) τ B x y smooth G e ζ ζ
  let base := fun ζ => ∏ k, outcomeObservationPatternWeight false Q S x₀ ℓ r h c w N τ B x G e ζ ζ k 0
  let cells := fun side ζ => eval (fun ka => U ka.1 ka.2)
    (mixedOutcomeComponentPolynomial Q side S x₀ ℓ r h a jb t ζ x y)
  let g := fun (s : I → CubicObservationChoice S) => (1 / 4 : ℝ) ^ Fintype.card I *
    |cubicObservationChoiceWeight (fun (i : I) (k : S) => linearPartition (localCoordinate x₀ r k.val (x i))) s|
  let choices := Finset.univ.erase (cubicZeroChoice : I → CubicObservationChoice S)
  let M := (2 * ((1 + N₀ / c + 1 / N₀ ^ 2) ^ 4) ^ Q) ^ Fintype.card S
  let scale := outcomeObservationScalarScale (Fintype.card I) N₀ jb (a * t)
  let R := M * ((5 : ℝ) ^ Fintype.card I * Fintype.card I * ((3 / 2 : ℝ) * |a * t * jb|))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hscale : 0 ≤ scale := outcomeObservationScalarScale_nonneg (Fintype.card I) N₀ jb (a * t) hN₀.le hjb hshift
  have hg : (∑ s ∈ choices, g s) ≤ (Fintype.card (I → CubicObservationChoice S) : ℝ) :=
    cubicObservation_normalized_weight_sum_bound (I := I) (K := S)
      (fun (i : I) (k : S) => linearPartition (localCoordinate x₀ r k.val (x i))) (fun i k => by
        rw [abs_of_nonneg (linearPartition_bounds _).1]
        exact (linearPartition_bounds _).2)
  have hf s (hs : s ∈ choices) : |independentSigns.expect (fun ζ => coeff ζ s * F s ζ ζ)| ≤ g s * (M * scale) :=
    outcome_observation_pattern_crude_bound Q hQ S x₀ ℓ r h c w N N₀ jb (a * t) τ hℓ hc hN₀ hN
      hm hrough hjb hsmall hshift hsjb B hB hreflect x y smooth hsmooth G e s (Finset.mem_erase.mp hs).1
  have hzero ζ : value ζ = (∑ s ∈ choices, coeff ζ s * F s ζ ζ) + base ζ * cells false ζ :=
    outcomeObservationValue_baseline true Q hQ S U x₀ ℓ r h c w N a jb t τ B x y G e ζ ζ
  have hbase ζ : |base ζ| ≤ M :=
    outcome_observation_baseline_bound Q S x₀ ℓ r h c w N N₀ τ hc hN₀ hN hm hrough B hB x G e ζ ζ
  have hjb1 : jb ≤ 1 := (le_mul_of_one_le_right hjb (by linarith : 1 ≤ 1 + N₀)).trans hsmall
  have hfield ζ (i : I) : |jb * physicalRoughField x₀ ℓ h ζ (x i)| ≤ 1 := by
    have hx : |physicalRoughField x₀ ℓ h ζ (x i)| ≤ N₀ := by
      rw [← physicalRoughWalsh_evaluate]
      exact (Walsh.evaluate_bound ζ _).trans (hrough _)
    rw [abs_mul, abs_of_nonneg hjb]
    exact (mul_le_mul_of_nonneg_left hx hjb).trans (by nlinarith)
  have hη (i : I) : |physicalRoughCorrection x₀ ℓ h (a * t) (x i)| ≤ 3 := by
    have he := physicalRoughCorrection_bounds x₀ ℓ h (a * t) hℓ (x i)
    rw [abs_of_nonneg he.1]
    exact he.2.trans (by nlinarith [pow_le_one₀ hshift (hsjb.trans hjb1) (n := 2)])
  have htarget : |a * t * jb| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hshift hjb)]
    exact (mul_le_mul (hsjb.trans hjb1) hjb1 hjb zero_le_one).trans_eq (one_mul 1)
  have hcells ζ : |cells true ζ - cells false ζ| ≤
      (5 : ℝ) ^ Fintype.card I * Fintype.card I * ((3 / 2 : ℝ) * |a * t * jb|) := by
    simpa only [cells, mixedOutcomeComponentPolynomial, map_prod] using
      mixedOutcomeCellProduct_sub_abs_le Q S (fun ka => U ka.1 ka.2) x₀ ℓ r h a jb t ζ x y
        (hfield ζ) hη hsmooth htarget
  have hdelta : |independentSigns.expect (fun ζ => base ζ * (cells true ζ - cells false ζ))| ≤ R := by
    apply FiniteLaw.abs_expect_le_bound
    intro ζ
    rw [abs_mul]
    exact mul_le_mul (hbase ζ) (hcells ζ) (abs_nonneg _) hM
  have he := finite_pattern_crude_comparison_bound independentSigns choices (fun ζ s => coeff ζ s * F s ζ ζ)
    value base cells g (M * scale) (Fintype.card (I → CubicObservationChoice S)) R
    (mul_nonneg hM hscale) hg hf hzero hdelta
  apply he.trans_eq
  dsimp only [M, scale, R, outcomeObservationScalarScale, outcomeCrudeConstant]
  rw [abs_of_nonneg (mul_nonneg hshift hjb)]
  simp only [cubicObservationChoices_card, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  ring

end CausalLowerbound.PartC



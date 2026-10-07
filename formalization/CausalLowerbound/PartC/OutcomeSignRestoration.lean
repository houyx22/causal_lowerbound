import CausalLowerbound.PartC.OutcomeCellDifference
import CausalLowerbound.PartC.PhysicalGhostOutcomePatterns
import CausalLowerbound.PartC.PropensitySignRestoration

/-! Restore the original shared signs after cubic likelihood matching.
The error on the zero carrier pattern is multiplied by the actual
likelihood difference and therefore keeps the target amplitude a*t*jb. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I]

theorem physical_outcome_increment_restoration_bound
    (Q : ℕ) (S : Finset (d → ℤ)) (U : S × CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (c w N N₀ a jb t : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1) (hshift : 0 ≤ a * t) (hsjb : a * t ≤ jb)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (hB : ∀ k, ‖B k‖ ≤ 2)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hsmooth : ∀ i, |a * eval U (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (T : Finset (activeBlocks (d := d) ℓ h)) :
    let W := fun (ζ η : activeBlocks (d := d) ℓ h → Bool) (k : S) =>
      ghostOutcomePatternIntegral x₀ ℓ r h k.val c w N (B k) (e k)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
        (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
          (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η 0 (fun _ => 1)
    let cells := fun side ζ => ∏ i, eval U (mixedOutcomeCellPolynomial Q side S x₀ ℓ r h a jb t ζ (x i) (y i))
    let C := 1 + N₀ / c + 1 / N₀ ^ 2
    let cost := fun k j => (C ^ 4) ^ Q * (2 * ‖symbolPart j (B k)‖ + (3 * ‖B k - unit‖) *
      ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))
    |independentSigns.expect (fun ζ => Walsh.resampleAverage T
        (fun η => (∏ k, W ζ η k) * (cells true ζ - cells false ζ)) ζ) -
      independentSigns.expect (fun ζ => (∏ k, W ζ ζ k) * (cells true ζ - cells false ζ))| ≤
      ((2 * (C ^ 4) ^ Q) ^ Fintype.card S * ∑ k, ∑ j ∈ T, cost k j) *
        ((5 : ℝ) ^ Fintype.card I * Fintype.card I * ((3 / 2 : ℝ) * |a * t * jb|)) := by
  dsimp only
  let C := 1 + N₀ / c + 1 / N₀ ^ 2
  let M := 2 * (C ^ 4) ^ Q
  let u := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
    carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
  let F := fun ζ (k : S) η => physicalGhostOutcomePatternWeight Q x₀ ℓ r h k.val c w N 0 (B k) (e k) (u k) ζ η 0
  let cost := fun (k : S) (j : activeBlocks (d := d) ℓ h) => (C ^ 4) ^ Q *
    (2 * ‖symbolPart j (B k)‖ + (3 * ‖B k - unit‖) *
      ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))
  let cells := fun side ζ => ∏ i, eval U (mixedOutcomeCellPolynomial Q side S x₀ ℓ r h a jb t ζ (x i) (y i))
  have hC : 1 ≤ C := by
    dsimp [C]
    have hcz : 0 ≤ N₀ / c := by positivity
    have hcκ : 0 ≤ 1 / N₀ ^ 2 := by positivity
    linarith
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [one_le_pow₀ (one_le_pow₀ hC (n := 4)) (n := Q)]
  have hNpos : 0 < N := (div_pos hN₀ hc).trans_le hN
  have hF ζ (k : S) η : |F ζ k η| ≤ M := by
    apply (physicalGhostOutcomePatternWeight_bound Q x₀ ℓ r h k.val c w N N₀ 0 hc hN₀ hN
      hm hrough (B k) (e k) (u k) ζ η 0).trans
    simpa only [M, mul_comm] using
      mul_le_mul_of_nonneg_left (hB k) (pow_nonneg (pow_nonneg (zero_le_one.trans hC) 4) Q)
  have hcost (k : S) (j : activeBlocks (d := d) ℓ h) : 0 ≤ cost k j := by
    dsimp [cost]
    have hC0 := zero_le_one.trans hC
    positivity
  have hchange ζ (k : S) j η η' (he : ∀ i, i ≠ j → η i = η' i) : |F ζ k η - F ζ k η'| ≤ cost k j :=
    physicalGhostOutcomePatternWeight_one_sign_bound Q x₀ ℓ r h k.val hℓ hr c w N N₀ 0 hc hN₀ hN
      hm hrough (B k) (e k) (u k) ζ 0 (fun v hv => (hv rfl).elim) j η η' he
  have hjb1 : jb ≤ 1 := (le_mul_of_one_le_right hjb (by linarith : 1 ≤ 1 + N₀)).trans hsmall
  have hfield ζ (i : I) : |jb * physicalRoughField x₀ ℓ h ζ (x i)| ≤ 1 := by
    have hx : |physicalRoughField x₀ ℓ h ζ (x i)| ≤ N₀ := by
      rw [← physicalRoughWalsh_evaluate]
      exact (Walsh.evaluate_bound ζ _).trans (hrough _)
    rw [abs_mul, abs_of_nonneg hjb]
    exact (mul_le_mul_of_nonneg_left hx hjb).trans (by nlinarith)
  have hη (i : I) : |physicalRoughCorrection x₀ ℓ h (a * t) (x i)| ≤ 3 := by
    have hh := physicalRoughCorrection_bounds x₀ ℓ h (a * t) hℓ (x i)
    rw [abs_of_nonneg hh.1]
    exact hh.2.trans (by nlinarith [pow_le_one₀ hshift (hsjb.trans hjb1) (n := 2)])
  have htarget : |a * t * jb| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hshift hjb)]
    exact (mul_le_mul (hsjb.trans hjb1) hjb1 hjb zero_le_one).trans_eq (one_mul 1)
  have hd ζ : |cells true ζ - cells false ζ| ≤
      (5 : ℝ) ^ Fintype.card I * Fintype.card I * ((3 / 2 : ℝ) * |a * t * jb|) :=
    mixedOutcomeCellProduct_sub_abs_le Q S U x₀ ℓ r h a jb t ζ x y (hfield ζ) hη hsmooth htarget
  have hb := resampled_product_increment_restoration_bound T F M hM hF cost hcost hchange
    (fun ζ => cells true ζ - cells false ζ) _ hd
  have hzero (k : S) : selectedOutcomeGhostTaper Q (e k) 0 (u k) (0 : Degree (Fin Q) 3) =
      (fun _ : G k → d → ℝ => (1 : ℝ)) := by
    funext g
    simp only [selectedOutcomeGhostTaper, if_pos rfl, if_true]
  simpa only [F, physicalGhostOutcomePatternWeight, hzero, M, C, cost, cells, u] using hb

end CausalLowerbound.PartC

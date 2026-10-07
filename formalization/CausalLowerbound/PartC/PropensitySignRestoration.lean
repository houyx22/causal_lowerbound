import CausalLowerbound.PartC.PropensityCellDifference
import CausalLowerbound.PartC.PhysicalGhostPatterns
import CausalLowerbound.PartC.ResamplingParity

/-! Restore the original shared signs on the matched likelihood increment.
The retained rough variables stay frozen during resampling, and the error
keeps the target amplitude ja * b * t. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {J K d I : Type*} [Fintype J] [DecidableEq J] [Fintype K]
  [Fintype d] [DecidableEq d] [Fintype I]

theorem resampled_product_increment_restoration_bound
    (T : Finset J) (F : (J → Bool) → K → (J → Bool) → ℝ)
    (M : ℝ) (hM : 1 ≤ M) (hF : ∀ ζ k η, |F ζ k η| ≤ M)
    (cost : K → J → ℝ) (hcost : ∀ k j, 0 ≤ cost k j)
    (hchange : ∀ ζ k j η η', (∀ i, i ≠ j → η i = η' i) → |F ζ k η - F ζ k η'| ≤ cost k j)
    (Δ : (J → Bool) → ℝ) (D : ℝ) (hΔ : ∀ ζ, |Δ ζ| ≤ D) :
    |independentSigns.expect (fun ζ => Walsh.resampleAverage T (fun η => (∏ k, F ζ k η) * Δ ζ) ζ) -
      independentSigns.expect (fun ζ => (∏ k, F ζ k ζ) * Δ ζ)| ≤
      (M ^ Fintype.card K * ∑ k, ∑ j ∈ T, cost k j) * D := by
  rw [← FiniteLaw.expect_sub]
  apply FiniteLaw.abs_expect_le_bound
  intro ζ
  have he := Walsh.resampleAverage_product_sub_bound T (F ζ) M hM (hF ζ) cost (hchange ζ) ζ
  have he' : |Walsh.resampleAverage T (fun η => ∏ k, F ζ k η) ζ - ∏ k, F ζ k ζ| ≤
      M ^ Fintype.card K * ∑ k, ∑ j ∈ T, cost k j := by
    rw [abs_sub_comm]
    exact he
  simp only [Walsh.resampleAverage, FiniteLaw.expect_mul_const, ← sub_mul, abs_mul]
  exact mul_le_mul he' (hΔ ζ) (abs_nonneg _) (mul_nonneg
    (pow_nonneg (zero_le_one.trans hM) _) (Finset.sum_nonneg (fun k _ =>
      Finset.sum_nonneg (fun j _ => hcost k j))))

theorem physical_propensity_increment_restoration_bound
    (Q : ℕ) (S : Finset (d → ℤ)) (U : S × CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (c w N N₀ ja b t : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hja : 0 ≤ ja) (hsmall : ja * (1 + N₀) ≤ 1) (htarget : |ja * b * t| ≤ 1)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1) (hB : ∀ k, ‖B k‖ ≤ 2)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hsmooth : ∀ i, |b * eval U (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (T : Finset (activeBlocks (d := d) ℓ h)) :
    let W := fun (ζ η : activeBlocks (d := d) ℓ h → Bool) (k : S) =>
      ghostPatternIntegral x₀ ℓ r h k.val c w N ja (B k) (e k)
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
        (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ
          (carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))) η ∅ (fun _ => 1)
    let cells := fun side ζ => ∏ i, eval U (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))
    let C := 1 + N₀ / c + 1 / (c * N₀)
    let cost := fun k j => C ^ Q * (2 * ‖symbolPart j (B k)‖ + ‖B k - unit‖ *
      ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))
    |independentSigns.expect (fun ζ => Walsh.resampleAverage T
        (fun η => (∏ k, W ζ η k) * (cells true ζ - cells false ζ)) ζ) -
      independentSigns.expect (fun ζ => (∏ k, W ζ ζ k) * (cells true ζ - cells false ζ))| ≤
      ((2 * C ^ Q) ^ Fintype.card S * ∑ k, ∑ j ∈ T, cost k j) *
        ((2 : ℝ) ^ Fintype.card I * Fintype.card I * (|ja * b * t| / 2)) := by
  dsimp only
  let C := 1 + N₀ / c + 1 / (c * N₀)
  let M := 2 * C ^ Q
  let u := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
    carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
  let F := fun ζ (k : S) η => physicalGhostPatternWeight Q x₀ ℓ r h k.val c w N ja 0 (B k) (e k) (u k) ζ η ∅
  let cost := fun (k : S) (j : activeBlocks (d := d) ℓ h) => C ^ Q * (2 * ‖symbolPart j (B k)‖ + ‖B k - unit‖ *
    ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))
  let cells := fun side ζ => ∏ i, eval U (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))
  have hC : 1 ≤ C := by
    dsimp [C]
    have hcz : 0 ≤ N₀ / c := by positivity
    have hcκ : 0 ≤ 1 / (c * N₀) := by positivity
    linarith
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [one_le_pow₀ hC (n := Q)]
  have hNpos : 0 < N := (div_pos hN₀ hc).trans_le hN
  have hja1 : ja ≤ 1 := (le_mul_of_one_le_right hja (by linarith : 1 ≤ 1 + N₀)).trans hsmall
  have hja2 : ja ^ 2 ≤ 1 := pow_le_one₀ hja hja1
  have hF ζ (k : S) η : |F ζ k η| ≤ M := by
    apply (physicalGhostPatternWeight_bound Q x₀ ℓ r h k.val c w N N₀ ja 0 hc hN₀ hN
      hm hrough hja2 (B k) (e k) (u k) ζ η ∅).trans
    simpa only [M, mul_comm] using mul_le_mul_of_nonneg_left (hB k) (pow_nonneg (zero_le_one.trans hC) Q)
  have hcost (k : S) (j : activeBlocks (d := d) ℓ h) : 0 ≤ cost k j := by
    dsimp [cost]
    positivity
  have hchange ζ (k : S) j η η' (he : ∀ i, i ≠ j → η i = η' i) : |F ζ k η - F ζ k η'| ≤ cost k j :=
    physicalGhostPatternWeight_one_sign_bound Q x₀ ℓ r h k.val hℓ hr c w N N₀ ja 0 hc hN₀ hN
      hm hrough hja2 (B k) (e k) (u k) ζ ∅ (fun v hv => by simpa using hv) j η η' he
  have hfield ζ (i : I) : |ja * physicalRoughField x₀ ℓ h ζ (x i)| ≤ 1 := by
    have hx : |physicalRoughField x₀ ℓ h ζ (x i)| ≤ N₀ := by
      rw [← physicalRoughWalsh_evaluate]
      exact (Walsh.evaluate_bound ζ _).trans (hrough _)
    rw [abs_mul, abs_of_nonneg hja]
    exact (mul_le_mul_of_nonneg_left hx hja).trans (by nlinarith)
  have hd ζ : |cells true ζ - cells false ζ| ≤
      (2 : ℝ) ^ Fintype.card I * Fintype.card I * (|ja * b * t| / 2) :=
    mixedPropensityCellProduct_sub_abs_le Q S U x₀ ℓ r h ja b t ζ x y (hfield ζ) hsmooth htarget
  have hb := resampled_product_increment_restoration_bound T F M hM hF cost hcost hchange
    (fun ζ => cells true ζ - cells false ζ) _ hd
  simpa only [F, physicalGhostPatternWeight, selectedGhostTaper, if_pos rfl, M, C, cost, cells, u] using hb

end CausalLowerbound.PartC

import CausalLowerbound.PartC.PhysicalGhostOutcomePatterns
import CausalLowerbound.PartC.ScalarResamplingParity
import CausalLowerbound.PartC.OutcomeTaylorBounds

/-! Shared-sign resampling for products of actual cubic ghost patterns and
actual normalized Taylor coefficients. All blocks use the same fresh sign
field. The error preserves shift times rough amplitude. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d K P : Type*} [Fintype d] [DecidableEq d] [Fintype K] [Fintype P]

theorem physical_ghost_outcome_pattern_resampling_bound
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (k : K → d → ℤ)
    (c w N N₀ jb τ shift : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hfield : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1) (hshift : 0 ≤ shift) (hsjb : shift ≤ jb)
    (I G : K → Type*) [∀ a, Fintype (I a)] [∀ a, Fintype (G a)]
    (e : ∀ a, I a ⊕ G a ≃ Fin Q) (u : ∀ a, I a → d → ℝ)
    (D : K → Degree (Fin Q) 3) (hD : 0 < ∑ a, degreeSize (D a))
    (hret : ∀ a v, D a v ≠ 0 → ∃ i : I a, e a (Sum.inl i) = v)
    (W : K → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (hW : ∀ a, ‖W a‖ ≤ 2) (hreflect : ∀ a, reflection (W a) = W a)
    (T : Finset (activeBlocks (d := d) ℓ h))
    (y : P → d → ℝ) (R A η smooth : P → ℝ) (f : P → Fin 4)
    (hR : ∀ i, |R i| ≤ 1) (hA : ∀ i, |A i| ≤ 1)
    (hη : ∀ i, |η i| ≤ 3) (hsmooth : ∀ i, |smooth i| ≤ 1) :
    let C := 1 + N₀ / c + 1 / N₀ ^ 2
    let F := fun a ζ ξ => physicalGhostOutcomePatternWeight Q x₀ ℓ r h (k a) c w N τ (W a) (e a) (u a) ζ ξ (D a)
    let cost := fun a j => (C ^ 4) ^ Q * (2 * ‖symbolPart j (W a)‖ + (3 * ‖W a - unit‖) *
      ((Fintype.card (G a) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))
    |independentSigns.expect (fun ζ => shift ^ (∑ a, degreeSize (D a)) *
      ((∏ a, F a ζ ζ) - Walsh.resampleAverage T (fun ξ => ∏ a, F a ζ ξ) ζ) *
        ∏ i, outcomeTaylorCoefficient (R i) (A i) 1 jb (η i) (smooth i)
          (physicalRoughField x₀ ℓ h ζ (y i)) (f i))| ≤
      ((2 * (C ^ 4) ^ Q) ^ Fintype.card K * ∑ a, ∑ j ∈ T, cost a j) *
        ((12 : ℝ) ^ Fintype.card P * ((Fintype.card P : ℝ) * 12 + 1)) *
          (shift * (jb * (1 + N₀))) := by
  dsimp only
  let C := 1 + N₀ / c + 1 / N₀ ^ 2
  let F := fun a ζ ξ => physicalGhostOutcomePatternWeight Q x₀ ℓ r h (k a) c w N τ (W a) (e a) (u a) ζ ξ (D a)
  let cost := fun a j => (C ^ 4) ^ Q * (2 * ‖symbolPart j (W a)‖ + (3 * ‖W a - unit‖) *
    ((Fintype.card (G a) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))
  have hcz : 0 ≤ N₀ / c := by positivity
  have hcκ : 0 ≤ 1 / N₀ ^ 2 := by positivity
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hM : 1 ≤ 2 * (C ^ 4) ^ Q := by nlinarith [one_le_pow₀ (one_le_pow₀ hC (n := 4)) (n := Q)]
  have hNp : 0 < N := (div_pos hN₀ hc).trans_le hN
  have hρ : 0 ≤ jb * (1 + N₀) := by positivity
  have hjb' : jb ≤ jb * (1 + N₀) := le_mul_of_one_le_right hjb (by linarith)
  have hF (a : K) ζ ξ : |F a ζ ξ| ≤ 2 * (C ^ 4) ^ Q := by
    have hb := physicalGhostOutcomePatternWeight_bound Q x₀ ℓ r h (k a) c w N N₀ τ hc hN₀ hN
      hm hfield (W a) (e a) (u a) ζ ξ (D a)
    exact hb.trans (by
      have hn := mul_le_mul_of_nonneg_left (hW a) (pow_nonneg (pow_nonneg (zero_le_one.trans hC) 4) Q)
      simpa only [C, mul_comm] using hn)
  have hp (a : K) ζ ξ : F a (Walsh.flip ζ) (Walsh.flip ξ) = (-1) ^ degreeSize (D a) * F a ζ ξ :=
    physicalGhostOutcomePatternWeight_parity Q x₀ ℓ r h (k a) c w N τ (W a) (hreflect a)
      (e a) (u a) ζ ξ (D a)
  have hcost (a : K) (j : activeBlocks (d := d) ℓ h) : 0 ≤ cost a j := by
    dsimp only [cost]
    have hC0 := zero_le_one.trans hC
    positivity
  have hs (a : K) ζ j ξ ξ' (he : ∀ i, i ≠ j → ξ i = ξ' i) :
      |F a ζ ξ - F a ζ ξ'| ≤ cost a j :=
    physicalGhostOutcomePatternWeight_one_sign_bound Q x₀ ℓ r h (k a) hℓ hr c w N N₀ τ hc hN₀ hN
      hm hfield (W a) (e a) (u a) ζ (D a) (hret a) j ξ ξ' he
  have hrough (i : P) ζ : |jb * physicalRoughField x₀ ℓ h ζ (y i)| ≤ jb * (1 + N₀) := by
    have hb : |physicalRoughField x₀ ℓ h ζ (y i)| ≤ N₀ := by
      rw [← physicalRoughWalsh_evaluate]
      exact (Walsh.evaluate_bound ζ _).trans (hfield _)
    rw [abs_mul, abs_of_nonneg hjb]
    exact mul_le_mul_of_nonneg_left (hb.trans (by linarith)) hjb
  have hg (i : P) ζ := outcomeTaylorCoefficient_unit_bounds (R i) (A i) jb (η i) (smooth i)
    (physicalRoughField x₀ ℓ h ζ (y i)) (jb * (1 + N₀))
    (hR i) (hA i) (hη i) (hsmooth i) hρ hsmall (hrough i ζ) (f i)
  have hb (i : P) : |outcomeTaylorBase (R i) (smooth i) (f i)| ≤ 12 :=
    (outcomeTaylorBase_bound (R i) (smooth i) (hR i) (hsmooth i) (f i)).trans (by norm_num)
  have hh := resampled_product_scalar_shift_bound T (fun a => degreeSize (D a)) hD F hp
    (2 * (C ^ 4) ^ Q) hM hF cost hcost hs
    (fun i ζ => outcomeTaylorCoefficient (R i) (A i) 1 jb (η i) (smooth i)
      (physicalRoughField x₀ ℓ h ζ (y i)) (f i))
    (fun i => outcomeTaylorBase (R i) (smooth i) (f i)) 12 shift (jb * (1 + N₀))
    (by norm_num) hshift hρ hsmall (hsjb.trans hjb') (fun i ζ => (hg i ζ).1) hb (fun i ζ => (hg i ζ).2)
  simpa only [C, F, cost] using hh

end CausalLowerbound.PartC

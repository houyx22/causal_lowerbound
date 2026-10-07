import CausalLowerbound.PartC.PhysicalGhostPatterns

/-! The shared-sign resampling estimate for products of actual physical
ghost-integrated patterns. Retained/ghost splits may differ between blocks.
The estimate keeps both the centered carrier norm and the physical
shift-times-rough factor, and uses the actual complete-graph taper. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d K P : Type*} [Fintype d] [DecidableEq d] [Fintype K] [Fintype P]

theorem physical_ghost_pattern_shift_resampling_bound
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (k : K → d → ℤ)
    (c w N N₀ ja τ shift : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hfield : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (hja : 0 ≤ ja) (hsmall : ja * (1 + N₀) ≤ 1) (hshift : 0 ≤ shift) (hsja : shift ≤ ja)
    (I G : K → Type*) [∀ a, Fintype (I a)] [∀ a, Fintype (G a)]
    (e : ∀ a, I a ⊕ G a ≃ Fin Q) (u : ∀ a, I a → d → ℝ)
    (A : K → Finset (Fin Q)) (hA : 0 < ∑ a, (A a).card)
    (hret : ∀ a v, v ∈ A a → ∃ i : I a, e a (Sum.inl i) = v)
    (W : K → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (hW : ∀ a, ‖W a‖ ≤ 2) (hreflect : ∀ a, reflection (W a) = W a)
    (T : Finset (activeBlocks (d := d) ℓ h))
    (y : P → d → ℝ) (R : P → ℝ) (hR : ∀ i, |R i| ≤ 1) :
    let C := 1 + N₀ / c + 1 / (c * N₀)
    let F := fun a ζ η => physicalGhostPatternWeight Q x₀ ℓ r h (k a) c w N ja τ (W a) (e a) (u a) ζ η (A a)
    let cost := fun a j => C ^ Q * (2 * ‖symbolPart j (W a)‖ + ‖W a - unit‖ *
      ((Fintype.card (G a) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))
    |independentSigns.expect (fun ζ => shift ^ (∑ a, (A a).card) *
      ((∏ a, F a ζ ζ) - Walsh.resampleAverage T (fun η => ∏ a, F a ζ η) ζ) *
        ∏ i, (1 + R i * ja * physicalRoughField x₀ ℓ h ζ (y i)))| ≤
      ((2 * C ^ Q) ^ Fintype.card K * ∑ a, ∑ j ∈ T, cost a j) * (2 : ℝ) ^ Fintype.card P *
        ((Fintype.card P : ℝ) + 1) * (shift * (ja * (1 + N₀))) := by
  dsimp only
  let C := 1 + N₀ / c + 1 / (c * N₀)
  let F := fun a ζ η => physicalGhostPatternWeight Q x₀ ℓ r h (k a) c w N ja τ (W a) (e a) (u a) ζ η (A a)
  let cost := fun a j => C ^ Q * (2 * ‖symbolPart j (W a)‖ + ‖W a - unit‖ *
    ((Fintype.card (G a) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))
  have hcz : 0 ≤ N₀ / c := by positivity
  have hcκ : 0 ≤ 1 / (c * N₀) := by positivity
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hM : 1 ≤ 2 * C ^ Q := by nlinarith [one_le_pow₀ hC (n := Q)]
  have hNp : 0 < N := (div_pos hN₀ hc).trans_le hN
  have hja' : ja ≤ ja * (1 + N₀) := le_mul_of_one_le_right hja (by linarith)
  have hja2 : ja ^ 2 ≤ 1 := pow_le_one₀ hja (hja'.trans hsmall)
  have hF (a : K) ζ η : |F a ζ η| ≤ 2 * C ^ Q := by
    have hb := physicalGhostPatternWeight_bound Q x₀ ℓ r h (k a) c w N N₀ ja τ hc hN₀ hN
      hm hfield hja2 (W a) (e a) (u a) ζ η (A a)
    exact hb.trans (by
      have hn := mul_le_mul_of_nonneg_left (hW a) (pow_nonneg (zero_le_one.trans hC) Q)
      simpa only [C, mul_comm] using hn)
  have hp (a : K) ζ η : F a (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ (A a).card * F a ζ η :=
    physicalGhostPatternWeight_parity Q x₀ ℓ r h (k a) c w N ja τ (W a) (hreflect a)
      (e a) (u a) ζ η (A a)
  have hcost (a : K) (j : activeBlocks (d := d) ℓ h) : 0 ≤ cost a j := by
    dsimp only [cost]
    have hC0 := zero_le_one.trans hC
    positivity
  have hs (a : K) ζ j η η' (he : ∀ i, i ≠ j → η i = η' i) :
      |F a ζ η - F a ζ η'| ≤ cost a j :=
    physicalGhostPatternWeight_one_sign_bound Q x₀ ℓ r h (k a) hℓ hr c w N N₀ ja τ hc hN₀ hN
      hm hfield hja2 (W a) (e a) (u a) ζ (A a) (hret a) j η η' he
  have hf (i : P) ζ : |R i * ja * physicalRoughField x₀ ℓ h ζ (y i)| ≤ ja * (1 + N₀) := by
    have hb : |physicalRoughField x₀ ℓ h ζ (y i)| ≤ N₀ := by
      rw [← physicalRoughWalsh_evaluate]
      exact (Walsh.evaluate_bound ζ _).trans (hfield _)
    rw [abs_mul, abs_mul, abs_of_nonneg hja]
    calc
      _ ≤ (1 * ja) * N₀ := mul_le_mul (mul_le_mul_of_nonneg_right (hR i) hja) hb
        (abs_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith
  have hb := resampled_product_shift_bound T (fun a => (A a).card) hA F hp
    (2 * C ^ Q) hM hF cost hcost hs (fun i ζ => R i * ja * physicalRoughField x₀ ℓ h ζ (y i))
    shift (ja * (1 + N₀)) hshift (by positivity) hsmall (hsja.trans hja') hf
  simpa only [C, F, cost] using hb

end CausalLowerbound.PartC

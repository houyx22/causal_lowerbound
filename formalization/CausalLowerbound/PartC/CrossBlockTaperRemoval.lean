import CausalLowerbound.PartC.GhostTaperRemoval

/-! Taper removal after one shared resampling retains the shift-times-
rough saving. Products of different block representatives use simultaneous
parity under the original sign law; no block independence is needed. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {J K P d : Type*} [Fintype J] [DecidableEq J] [Fintype K]
  [Fintype P] [Fintype d] [DecidableEq d]

theorem resampled_product_comparison_shift_bound
    (T : Finset J) (e : K → ℕ) (he : 0 < ∑ k, e k)
    (F G : K → (J → Bool) → (J → Bool) → ℝ)
    (hFp : ∀ k ζ η, F k (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ e k * F k ζ η)
    (hGp : ∀ k ζ η, G k (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ e k * G k ζ η)
    (M : ℝ) (hM : 1 ≤ M) (hF : ∀ k ζ η, |F k ζ η| ≤ M) (hG : ∀ k ζ η, |G k ζ η| ≤ M)
    (cost : K → ℝ) (hcost : ∀ k, 0 ≤ cost k) (hdiff : ∀ k ζ η, |F k ζ η - G k ζ η| ≤ cost k)
    (f : P → (J → Bool) → ℝ) (shift rough : ℝ)
    (hshift : 0 ≤ shift) (hrough : 0 ≤ rough) (hr1 : rough ≤ 1) (hsr : shift ≤ rough)
    (hf : ∀ i ζ, |f i ζ| ≤ rough) :
    |independentSigns.expect (fun ζ => shift ^ (∑ k, e k) *
      Walsh.resampleAverage T (fun η => (∏ k, F k ζ η) - ∏ k, G k ζ η) ζ *
        ∏ i, (1 + f i ζ))| ≤
      (M ^ Fintype.card K * ∑ k, cost k) * (2 : ℝ) ^ Fintype.card P *
        ((Fintype.card P : ℝ) + 1) * (shift * rough) := by
  let H := fun ζ η => (∏ k, F k ζ η) - ∏ k, G k ζ η
  have hp ζ η : H (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ (∑ k, e k) * H ζ η := by
    simp only [H, hFp, hGp, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_sub]
  have hbound ζ η : |H ζ η| ≤ M ^ Fintype.card K * ∑ k, cost k := by
    have hb := abs_prod_sub_prod_le_bounded Finset.univ (fun k => F k ζ η) (fun k => G k ζ η)
      M hM (fun k _ => hF k ζ η) (fun k _ => hG k ζ η)
    simp only [Finset.card_univ] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hdiff k ζ η))
      (pow_nonneg (zero_le_one.trans hM) _))
  exact parity_weighted_shift_bound (∑ k, e k) he (fun ζ => Walsh.resampleAverage T (H ζ) ζ)
    (Walsh.resampleAverage_simultaneous_parity T H _ hp) f
    (M ^ Fintype.card K * ∑ k, cost k) shift rough
    (mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) (Finset.sum_nonneg (fun k _ => hcost k)))
    hshift hrough hr1 hsr (fun ζ => FiniteLaw.abs_expect_le_bound _ _ _ (fun fresh =>
      hbound ζ (Walsh.resample T ζ fresh))) hf

theorem physical_ghost_taper_shift_bound
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : K → d → ℤ)
    (c w N N₀ ja τ shift : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hfield : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (hja : 0 ≤ ja) (hsmall : ja * (1 + N₀) ≤ 1) (hshift : 0 ≤ shift) (hsja : shift ≤ ja)
    (I G : K → Type*) [∀ a, Fintype (I a)] [∀ a, Fintype (G a)]
    (e : ∀ a, I a ⊕ G a ≃ Fin Q) (u : ∀ a, I a → d → ℝ)
    (A : K → Finset (Fin Q)) (hA : 0 < ∑ a, (A a).card)
    (B : K → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (hB : ∀ a, ‖B a‖ ≤ 2) (hreflect : ∀ a, reflection (B a) = B a)
    (T : Finset (activeBlocks (d := d) ℓ h)) (y : P → d → ℝ) (R : P → ℝ) (hR : ∀ i, |R i| ≤ 1) :
    let C := 1 + N₀ / c + 1 / (c * N₀)
    let F := fun a ζ η => physicalGhostPatternWeight Q x₀ ℓ r h (k a) c w N ja τ (B a) (e a) (u a) ζ η (A a)
    let W := fun a ζ η => ghostPatternIntegral x₀ ℓ r h (k a) c w N ja (B a) (e a) (u a)
      (fun i => normalizedRoughChart x₀ ℓ r h (k a) c w N ζ (u a i)) η (A a) (fun _ => 1)
    |independentSigns.expect (fun ζ => shift ^ (∑ a, (A a).card) *
      Walsh.resampleAverage T (fun η => (∏ a, F a ζ η) - ∏ a, W a ζ η) ζ *
        ∏ i, (1 + R i * ja * physicalRoughField x₀ ℓ h ζ (y i)))| ≤
      ((2 * C ^ Q) ^ Fintype.card K * ∑ a, (2 * C ^ Q) * completedGhostTaperDefect Q (e a) τ (u a)) *
        (2 : ℝ) ^ Fintype.card P * ((Fintype.card P : ℝ) + 1) * (shift * (ja * (1 + N₀))) := by
  dsimp only
  let C := 1 + N₀ / c + 1 / (c * N₀)
  let M := 2 * C ^ Q
  let F := fun a ζ η => physicalGhostPatternWeight Q x₀ ℓ r h (k a) c w N ja τ (B a) (e a) (u a) ζ η (A a)
  let W := fun a ζ η => ghostPatternIntegral x₀ ℓ r h (k a) c w N ja (B a) (e a) (u a)
    (fun i => normalizedRoughChart x₀ ℓ r h (k a) c w N ζ (u a i)) η (A a) (fun _ => 1)
  let cost := fun a => M * completedGhostTaperDefect Q (e a) τ (u a)
  have hcz : 0 ≤ N₀ / c := by positivity
  have hcκ : 0 ≤ 1 / (c * N₀) := by positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCz : N₀ / c ≤ C := by dsimp [C]; linarith
  have hCκ : 1 / (c * N₀) ≤ C := by dsimp [C]; linarith
  have hM : 1 ≤ M := by dsimp [M]; nlinarith [one_le_pow₀ hC (n := Q)]
  have hja' : ja ≤ ja * (1 + N₀) := le_mul_of_one_le_right hja (by linarith)
  have hja2 : ja ^ 2 ≤ 1 := pow_le_one₀ hja (hja'.trans hsmall)
  have hn (a : K) : C ^ Q * ‖B a‖ ≤ M := by
    have hb := mul_le_mul_of_nonneg_left (hB a) (pow_nonneg (zero_le_one.trans hC) Q)
    simpa only [M, mul_comm] using hb
  have hF (a : K) ζ η : |F a ζ η| ≤ M :=
    (physicalGhostPatternWeight_bound Q x₀ ℓ r h (k a) c w N N₀ ja τ hc hN₀ hN hm hfield hja2
      (B a) (e a) (u a) ζ η (A a)).trans (hn a)
  have hW (a : K) ζ η : |W a ζ η| ≤ M := by
    have hb := ghostPatternIntegral_bound x₀ ℓ r h (k a) c w N N₀ ja hc hN₀ hN hm hfield hja2
      (B a) (e a) (u a) _
      (fun i => normalizedRoughChart_bound x₀ ℓ r h (k a) c w N N₀ hc hN₀ hN hm hfield ζ (u a i))
      C hC hCz hCκ (fun i =>
        (normalizedRoughChart_scaled_bound x₀ ℓ r h (k a) c w N N₀ hc hN₀ hN hm hfield ζ (u a i)).trans hCz)
      η (A a) (fun _ => 1) (fun _ => by norm_num)
    apply le_trans ?_ (hn a)
    simpa only [Fintype.card_fin] using hb
  have hFp (a : K) ζ η : F a (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ (A a).card * F a ζ η :=
    physicalGhostPatternWeight_parity Q x₀ ℓ r h (k a) c w N ja τ (B a) (hreflect a) (e a) (u a) ζ η (A a)
  have hWp (a : K) ζ η : W a (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ (A a).card * W a ζ η :=
    ghostPatternIntegral_simultaneous_parity x₀ ℓ r h (k a) c w N ja (B a) (hreflect a) (e a) (u a)
      (fun ξ i => normalizedRoughChart x₀ ℓ r h (k a) c w N ξ (u a i))
      (fun ξ i => normalizedRoughChart_flip x₀ ℓ r h (k a) c w N ξ (u a i)) ζ η (A a) (fun _ => 1)
  have hcost (a : K) : 0 ≤ cost a :=
    mul_nonneg (zero_le_one.trans hM) (completedGhostTaperDefect_bounds Q (e a) τ (u a)).1
  have hdiff (a : K) ζ η : |F a ζ η - W a ζ η| ≤ cost a :=
    (physicalGhostPatternWeight_taper_removal_bound Q x₀ ℓ r h (k a) c w N N₀ ja τ hc hN₀ hN hm hfield hja2
      (B a) (e a) (u a) ζ η (A a)).trans (mul_le_mul_of_nonneg_right (hn a)
        (completedGhostTaperDefect_bounds Q (e a) τ (u a)).1)
  have hf (i : P) ζ : |R i * ja * physicalRoughField x₀ ℓ h ζ (y i)| ≤ ja * (1 + N₀) := by
    have hb : |physicalRoughField x₀ ℓ h ζ (y i)| ≤ N₀ := by
      rw [← physicalRoughWalsh_evaluate]
      exact (Walsh.evaluate_bound ζ _).trans (hfield _)
    rw [abs_mul, abs_mul, abs_of_nonneg hja]
    calc
      _ ≤ (1 * ja) * N₀ := mul_le_mul (mul_le_mul_of_nonneg_right (hR i) hja) hb (abs_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith
  exact resampled_product_comparison_shift_bound T (fun a => (A a).card) hA F W hFp hWp M hM hF hW
    cost hcost hdiff (fun i ζ => R i * ja * physicalRoughField x₀ ℓ h ζ (y i)) shift (ja * (1 + N₀))
    hshift (by positivity) hsmall (hsja.trans hja') hf

end CausalLowerbound.PartC

import CausalLowerbound.PartC.OutcomeObservationComparison
import CausalLowerbound.PartC.PropensityErrorReduction

/-! Reduce the cubic comparison to a geometric sign cost and the actual
completed ghost defects. The constants depend only on fixed local counts. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def outcomeSignCost
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)] : ℝ :=
  outcomeObservationSignCost Q S ℓ r h c N N₀ B G
    (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i)))

def outcomePatternScale (q k : ℕ) (N₀ : ℝ) : ℝ :=
  (1 + (k : ℝ) + (k : ℝ) ^ 2 + (k : ℝ) ^ 3) ^ q *
    (12 : ℝ) ^ q * ((q : ℝ) * 12 + 1) * (1 + N₀)

def outcomeErrorConstant (Q q k D : ℕ) (c N₀ M : ℝ) : ℝ :=
  let C := 1 + N₀ / c + 1 / N₀ ^ 2
  (outcomePatternScale q k N₀ + (5 : ℝ) ^ q * q * (3 / 2 : ℝ)) * (2 * (C ^ 4) ^ Q) ^ k *
    ((C ^ 4) ^ Q * ((q : ℝ) * 2 ^ D) * (2 * M + 18 * Q / N₀) + 2 * (C ^ 4) ^ Q)

theorem outcomeErrorConstant_nonneg (Q q k D : ℕ) (c N₀ M : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hM : 0 ≤ M) :
    0 ≤ outcomeErrorConstant Q q k D c N₀ M := by
  unfold outcomeErrorConstant outcomePatternScale
  positivity

theorem outcomeComparisonError_factor
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ a jb t τ : ℝ)
    (hshift : 0 ≤ a * t) (hjb : 0 ≤ jb)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G e =
      (a * t * jb) *
        ((outcomePatternScale (Fintype.card I) (Fintype.card S) N₀ +
          (5 : ℝ) ^ Fintype.card I * Fintype.card I * (3 / 2 : ℝ)) *
            outcomeSignCost Q S x₀ ℓ r h c N N₀ B x G +
        outcomePatternScale (Fintype.card I) (Fintype.card S) N₀ *
          (2 * ((1 + N₀ / c + 1 / N₀ ^ 2) ^ 4) ^ Q) ^ Fintype.card S *
          (2 * ((1 + N₀ / c + 1 / N₀ ^ 2) ^ 4) ^ Q) *
          propensityGhostDefectSum Q S x₀ r τ x G e) := by
  unfold outcomeObservationComparisonError outcomePatternScale outcomeSignCost
    outcomeObservationTaperCost outcomeObservationScalarScale propensityGhostDefectSum
  rw [abs_of_nonneg (mul_nonneg hshift hjb)]
  simp only [cubicObservationChoices_card, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    ← Finset.mul_sum]
  ring

theorem outcomeSignCost_bound
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ M : ℝ)
    (hℓ : 0 ≤ ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hM : 0 ≤ M)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (hB : ∀ k, ‖B k‖ ≤ 2)
    (hsym : ∀ k j, ‖symbolPart j (B k)‖ ≤ M * (ℓ / (2 * r)) ^ Fintype.card d)
    (x : I → d → ℝ) (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    outcomeSignCost Q S x₀ ℓ r h c N N₀ B x G ≤
      (2 * ((1 + N₀ / c + 1 / N₀ ^ 2) ^ 4) ^ Q) ^ Fintype.card S *
        (((1 + N₀ / c + 1 / N₀ ^ 2) ^ 4) ^ Q *
          ((Fintype.card I : ℝ) * 2 ^ Fintype.card d) * (2 * M + 18 * Q / N₀)) *
        ((Fintype.card S : ℝ) * (ℓ / (2 * r)) ^ Fintype.card d) := by
  let C := (1 + N₀ / c + 1 / N₀ ^ 2) ^ 4
  let g := (ℓ / (2 * r)) ^ Fintype.card d
  let T := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg : 0 ≤ g := pow_nonneg (div_nonneg hℓ (by positivity)) _
  have hN' : N₀ ≤ c * N := by
    have he := (div_le_iff₀ hc).mp hN
    nlinarith
  have hi : 2 / (c * N) ≤ 2 / N₀ := div_le_div_of_nonneg_left (by norm_num) hN₀ hN'
  have hic : 0 ≤ 2 / (c * N) := div_nonneg (by norm_num) (hN₀.le.trans hN')
  have hG (k : S) : (Fintype.card (G k) : ℝ) ≤ Q := by
    have he := Fintype.card_congr (e k)
    simp only [Fintype.card_sum, Fintype.card_fin] at he
    exact_mod_cast (show Fintype.card (G k) ≤ Q by omega)
  have hu (k : S) : 3 * ‖B k - unit‖ ≤ 9 := by
    have he := norm_sub_le (B k) unit
    rw [unit_norm] at he
    linarith [hB k]
  have ht (k : S) (j : activeBlocks (d := d) ℓ h) :
      C ^ Q * (2 * ‖symbolPart j (B k)‖ + (3 * ‖B k - unit‖) *
        ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * g))) ≤
      C ^ Q * (2 * M + 18 * Q / N₀) * g := by
    have hh : (Fintype.card (G k) : ℝ) * ((2 / (c * N)) * g) ≤ (Q : ℝ) * ((2 / N₀) * g) :=
      mul_le_mul (hG k) (mul_le_mul_of_nonneg_right hi hg) (mul_nonneg hic hg) (Nat.cast_nonneg Q)
    have hb := mul_le_mul (hu k) hh
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hic hg)) (by norm_num : (0 : ℝ) ≤ 9)
    calc
      _ ≤ C ^ Q * (2 * (M * g) + 9 * ((Q : ℝ) * ((2 / N₀) * g))) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (hsym k j) (by norm_num)) hb)
          (pow_nonneg hC Q)
      _ = _ := by ring
  have hT : (T.card : ℝ) ≤ (Fintype.card I : ℝ) * 2 ^ Fintype.card d := by
    exact_mod_cast physicalLocalSigns_union_card x₀ ℓ h x
  have hk (k : S) :
      (∑ j ∈ T, C ^ Q * (2 * ‖symbolPart j (B k)‖ + (3 * ‖B k - unit‖) *
        ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * g)))) ≤
      ((Fintype.card I : ℝ) * 2 ^ Fintype.card d) * (C ^ Q * (2 * M + 18 * Q / N₀) * g) := by
    apply (Finset.sum_le_sum (fun j _ => ht k j)).trans
    simpa only [Finset.sum_const, nsmul_eq_mul] using mul_le_mul_of_nonneg_right hT
      (mul_nonneg (mul_nonneg (pow_nonneg hC Q) (by positivity)) hg)
  change (2 * C ^ Q) ^ Fintype.card S * (∑ k, _) ≤ _
  calc
    _ ≤ (2 * C ^ Q) ^ Fintype.card S * ∑ _k : S,
        ((Fintype.card I : ℝ) * 2 ^ Fintype.card d) * (C ^ Q * (2 * M + 18 * Q / N₀) * g) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hk k)) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, C, g]; ring

theorem outcomeComparisonError_geometric_bound
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ a jb t τ M : ℝ)
    (hℓ : 0 ≤ ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hM : 0 ≤ M)
    (hshift : 0 ≤ a * t) (hjb : 0 ≤ jb)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (hB : ∀ k, ‖B k‖ ≤ 2)
    (hsym : ∀ k j, ‖symbolPart j (B k)‖ ≤ M * (ℓ / (2 * r)) ^ Fintype.card d)
    (x : I → d → ℝ) (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G e ≤
      (a * t * jb) * outcomeErrorConstant Q (Fintype.card I) (Fintype.card S) (Fintype.card d) c N₀ M *
        ((Fintype.card S : ℝ) * (ℓ / (2 * r)) ^ Fintype.card d +
          propensityGhostDefectSum Q S x₀ r τ x G e) := by
  let C := (1 + N₀ / c + 1 / N₀ ^ 2) ^ 4
  let P := outcomePatternScale (Fintype.card I) (Fintype.card S) N₀
  let H := P + (5 : ℝ) ^ Fintype.card I * Fintype.card I * (3 / 2 : ℝ)
  let F := (2 * C ^ Q) ^ Fintype.card S
  let V := C ^ Q * ((Fintype.card I : ℝ) * 2 ^ Fintype.card d) * (2 * M + 18 * Q / N₀)
  let Z := 2 * C ^ Q
  let g := (Fintype.card S : ℝ) * (ℓ / (2 * r)) ^ Fintype.card d
  let D := propensityGhostDefectSum Q S x₀ r τ x G e
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hP : 0 ≤ P := by dsimp [P, outcomePatternScale]; positivity
  have hPH : P ≤ H := by
    dsimp only [H]
    exact le_add_of_nonneg_right (by positivity)
  have hH : 0 ≤ H := hP.trans hPH
  have hF : 0 ≤ F := pow_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC Q)) _
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hZ : 0 ≤ Z := mul_nonneg (by norm_num) (pow_nonneg hC Q)
  have hg : 0 ≤ g := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg hℓ (by positivity)) _)
  have hD : 0 ≤ D := (propensityGhostDefectSum_bounds Q S x₀ r τ x G e).1
  have hsign := outcomeSignCost_bound Q S x₀ ℓ r h c N N₀ M hℓ hr hc hN₀ hN hM B hB hsym x G e
  change outcomeSignCost Q S x₀ ℓ r h c N N₀ B x G ≤ F * V * g at hsign
  have hmix : H * outcomeSignCost Q S x₀ ℓ r h c N N₀ B x G + P * F * Z * D ≤
      (H * F * (V + Z)) * (g + D) := by
    calc
      _ ≤ H * (F * V * g) + P * F * Z * D :=
        add_le_add_right (mul_le_mul_of_nonneg_left hsign hH) _
      _ ≤ H * (F * V * g) + H * F * Z * D := by
        have he := mul_le_mul_of_nonneg_right hPH (mul_nonneg (mul_nonneg hF hZ) hD)
        nlinarith
      _ = H * F * (V * g + Z * D) := by ring
      _ ≤ H * F * ((V + Z) * (g + D)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hV hD, mul_nonneg hZ hg])
          (mul_nonneg hH hF)
      _ = _ := by ring
  rw [outcomeComparisonError_factor Q S x₀ ℓ r h c N N₀ a jb t τ hshift hjb B x G e]
  change (a * t * jb) * (H * outcomeSignCost Q S x₀ ℓ r h c N N₀ B x G + P * F * Z * D) ≤
    (a * t * jb) * (H * F * (V + Z)) * (g + D)
  exact (mul_le_mul_of_nonneg_left hmix (mul_nonneg hshift hjb)).trans_eq (by ring)

end CausalLowerbound.PartC

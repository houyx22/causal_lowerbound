import CausalLowerbound.PartC.AveragedPropensityComparison
import CausalLowerbound.PartC.PhysicalLocalPropensityMatching

/-! Reduce the actual comparison error to a geometric sign factor and
the sum of completed ghost-taper defects. All coefficients depend only
on the local observation/block counts and fixed carrier bounds. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def propensitySignCost
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)] : ℝ :=
  let T := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))
  let C := 1 + N₀ / c + 1 / (c * N₀)
  (2 * C ^ Q) ^ Fintype.card S * ∑ k, ∑ j ∈ T,
    C ^ Q * (2 * ‖symbolPart j (B k)‖ + ‖B k - unit‖ *
      ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))

def propensityGhostDefectSum
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r τ : ℝ) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) : ℝ :=
  ∑ k, completedGhostTaperDefect Q (e k) τ
    (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))

def propensityPatternScale (q k : ℕ) (N₀ : ℝ) : ℝ :=
  ((k : ℝ) + 1) ^ q * (2 : ℝ) ^ q * ((q : ℝ) + 1) * (1 + N₀)

def propensityErrorConstant (Q q k D : ℕ) (c N₀ M : ℝ) : ℝ :=
  let C := 1 + N₀ / c + 1 / (c * N₀)
  (propensityPatternScale q k N₀ + (2 : ℝ) ^ q * q / 2) * (2 * C ^ Q) ^ k *
    (C ^ Q * ((q : ℝ) * 2 ^ D) * (2 * M + 6 * Q / N₀) + 2 * C ^ Q)

theorem propensityErrorConstant_nonneg (Q q k D : ℕ) (c N₀ M : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hM : 0 ≤ M) :
    0 ≤ propensityErrorConstant Q q k D c N₀ M := by
  unfold propensityErrorConstant propensityPatternScale
  positivity

theorem propensityGhostDefectSum_bounds
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r τ : ℝ) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    0 ≤ propensityGhostDefectSum Q S x₀ r τ x G e ∧
      propensityGhostDefectSum Q S x₀ r τ x G e ≤ Fintype.card S := by
  constructor
  · exact Finset.sum_nonneg (fun k _ => (completedGhostTaperDefect_bounds Q (e k) τ _).1)
  · exact (Finset.sum_le_sum (fun k _ => (completedGhostTaperDefect_bounds Q (e k) τ _).2)).trans_eq
      (by simp)

theorem propensityComparisonError_factor
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ ja b t τ : ℝ)
    (hja : 0 ≤ ja) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ B x G e =
      (ja * b * t) *
        ((propensityPatternScale (Fintype.card I) (Fintype.card S) N₀ +
          (2 : ℝ) ^ Fintype.card I * Fintype.card I / 2) *
            propensitySignCost Q S x₀ ℓ r h c N N₀ B x G +
        propensityPatternScale (Fintype.card I) (Fintype.card S) N₀ *
          (2 * (1 + N₀ / c + 1 / (c * N₀)) ^ Q) ^ Fintype.card S *
          (2 * (1 + N₀ / c + 1 / (c * N₀)) ^ Q) *
          propensityGhostDefectSum Q S x₀ r τ x G e) := by
  have ha : |ja * b * t| = ja * b * t := abs_of_nonneg (mul_nonneg (mul_nonneg hja hb) ht)
  unfold propensityComparisonError propensityPatternScale propensitySignCost propensityGhostDefectSum
  rw [ha]
  simp only [← Finset.mul_sum]
  ring

theorem propensitySignCost_bound
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ M : ℝ)
    (hℓ : 0 ≤ ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hM : 0 ≤ M)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (hB : ∀ k, ‖B k‖ ≤ 2)
    (hsym : ∀ k j, ‖symbolPart j (B k)‖ ≤ M * (ℓ / (2 * r)) ^ Fintype.card d)
    (x : I → d → ℝ) (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    propensitySignCost Q S x₀ ℓ r h c N N₀ B x G ≤
      (2 * (1 + N₀ / c + 1 / (c * N₀)) ^ Q) ^ Fintype.card S *
        ((1 + N₀ / c + 1 / (c * N₀)) ^ Q *
          ((Fintype.card I : ℝ) * 2 ^ Fintype.card d) * (2 * M + 6 * Q / N₀)) *
        ((Fintype.card S : ℝ) * (ℓ / (2 * r)) ^ Fintype.card d) := by
  let C := 1 + N₀ / c + 1 / (c * N₀)
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
  have hu (k : S) : ‖B k - unit‖ ≤ 3 := by
    have he := norm_sub_le (B k) unit
    rw [unit_norm] at he
    linarith [hB k]
  have ht (k : S) (j : activeBlocks (d := d) ℓ h) :
      C ^ Q * (2 * ‖symbolPart j (B k)‖ + ‖B k - unit‖ *
        ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * g))) ≤
      C ^ Q * (2 * M + 6 * Q / N₀) * g := by
    have hh : (Fintype.card (G k) : ℝ) * ((2 / (c * N)) * g) ≤ (Q : ℝ) * ((2 / N₀) * g) :=
      mul_le_mul (hG k) (mul_le_mul_of_nonneg_right hi hg) (mul_nonneg hic hg) (Nat.cast_nonneg Q)
    have hb := mul_le_mul (hu k) hh
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hic hg)) (by norm_num : (0 : ℝ) ≤ 3)
    calc
      _ ≤ C ^ Q * (2 * (M * g) + 3 * ((Q : ℝ) * ((2 / N₀) * g))) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (hsym k j) (by norm_num)) hb)
          (pow_nonneg hC Q)
      _ = _ := by ring
  have hT : (T.card : ℝ) ≤ (Fintype.card I : ℝ) * 2 ^ Fintype.card d := by
    exact_mod_cast physicalLocalSigns_union_card x₀ ℓ h x
  have hk (k : S) :
      (∑ j ∈ T, C ^ Q * (2 * ‖symbolPart j (B k)‖ + ‖B k - unit‖ *
        ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * g)))) ≤
      ((Fintype.card I : ℝ) * 2 ^ Fintype.card d) * (C ^ Q * (2 * M + 6 * Q / N₀) * g) := by
    apply (Finset.sum_le_sum (fun j _ => ht k j)).trans
    simpa only [Finset.sum_const, nsmul_eq_mul] using mul_le_mul_of_nonneg_right hT
      (mul_nonneg (mul_nonneg (pow_nonneg hC Q) (by positivity)) hg)
  change (2 * C ^ Q) ^ Fintype.card S * (∑ k, _) ≤ _
  calc
    _ ≤ (2 * C ^ Q) ^ Fintype.card S * ∑ _k : S,
        ((Fintype.card I : ℝ) * 2 ^ Fintype.card d) * (C ^ Q * (2 * M + 6 * Q / N₀) * g) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hk k)) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, C, g]; ring

theorem propensityComparisonError_geometric_bound
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ ja b t τ M : ℝ)
    (hℓ : 0 ≤ ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hM : 0 ≤ M)
    (hja : 0 ≤ ja) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1) (hB : ∀ k, ‖B k‖ ≤ 2)
    (hsym : ∀ k j, ‖symbolPart j (B k)‖ ≤ M * (ℓ / (2 * r)) ^ Fintype.card d)
    (x : I → d → ℝ) (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ B x G e ≤
      (ja * b * t) * propensityErrorConstant Q (Fintype.card I) (Fintype.card S) (Fintype.card d) c N₀ M *
        ((Fintype.card S : ℝ) * (ℓ / (2 * r)) ^ Fintype.card d +
          propensityGhostDefectSum Q S x₀ r τ x G e) := by
  let C := 1 + N₀ / c + 1 / (c * N₀)
  let P := propensityPatternScale (Fintype.card I) (Fintype.card S) N₀
  let H := P + (2 : ℝ) ^ Fintype.card I * Fintype.card I / 2
  let F := (2 * C ^ Q) ^ Fintype.card S
  let V := C ^ Q * ((Fintype.card I : ℝ) * 2 ^ Fintype.card d) * (2 * M + 6 * Q / N₀)
  let Z := 2 * C ^ Q
  let g := (Fintype.card S : ℝ) * (ℓ / (2 * r)) ^ Fintype.card d
  let D := propensityGhostDefectSum Q S x₀ r τ x G e
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hP : 0 ≤ P := by dsimp [P, propensityPatternScale]; positivity
  have hPH : P ≤ H := by
    dsimp only [H]
    exact le_add_of_nonneg_right (by positivity)
  have hH : 0 ≤ H := hP.trans hPH
  have hF : 0 ≤ F := pow_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC Q)) _
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hZ : 0 ≤ Z := mul_nonneg (by norm_num) (pow_nonneg hC Q)
  have hg : 0 ≤ g := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg hℓ (by positivity)) _)
  have hD : 0 ≤ D := (propensityGhostDefectSum_bounds Q S x₀ r τ x G e).1
  have hsign := propensitySignCost_bound Q S x₀ ℓ r h c N N₀ M hℓ hr hc hN₀ hN hM B hB hsym x G e
  change propensitySignCost Q S x₀ ℓ r h c N N₀ B x G ≤ F * V * g at hsign
  have hmix : H * propensitySignCost Q S x₀ ℓ r h c N N₀ B x G + P * F * Z * D ≤
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
  rw [propensityComparisonError_factor Q S x₀ ℓ r h c N N₀ ja b t τ hja hb ht B x G e]
  change (ja * b * t) * (H * propensitySignCost Q S x₀ ℓ r h c N N₀ B x G + P * F * Z * D) ≤
    (ja * b * t) * (H * F * (V + Z)) * (g + D)
  exact (mul_le_mul_of_nonneg_left hmix (mul_nonneg (mul_nonneg hja hb) ht)).trans_eq (by ring)

end CausalLowerbound.PartC

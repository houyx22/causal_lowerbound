import CausalLowerbound.PartC.PropensityErrorReduction
import CausalLowerbound.PartC.GhostDefectReindex

/-! Remove the completion-permutation average and square the geometric
comparison bound without squaring the ghost defect. This preserves its
integrable first-moment cost and gives a constant uniform over small
components. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem propensityGhostDefectSum_completion
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r τ : ℝ) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e e' : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    propensityGhostDefectSum Q S x₀ r τ x G e = propensityGhostDefectSum Q S x₀ r τ x G e' := by
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Function.comp_def, Equiv.refl_apply] using completedGhostTaperDefect_reindex Q τ
    (e k) (e' k) (Equiv.refl _) (Equiv.refl _)
    (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))

theorem propensityComparisonError_completion
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ ja b t τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e e' : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ B x G e =
      propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ B x G e' := by
  have he (k : S) : completedGhostTaperDefect Q (e k) τ
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) =
      completedGhostTaperDefect Q (e' k) τ
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) := by
    simpa only [Function.comp_def, Equiv.refl_apply] using completedGhostTaperDefect_reindex Q τ
      (e k) (e' k) (Equiv.refl _) (Equiv.refl _)
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
  simp only [propensityComparisonError, he]

theorem propensityComparisonError_permutation_average
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ ja b t τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (fun σ =>
      propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ B x G (fun k => (e k).trans (σ k).symm)) =
      propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ B x G e := by
  calc
    _ = (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (fun _ =>
        propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ B x G e) :=
      FiniteLaw.expect_congr _ (fun σ => propensityComparisonError_completion
        Q S x₀ ℓ r h c N N₀ ja b t τ B x G _ e)
    _ = _ := FiniteLaw.expect_const _ _

theorem propensityComparisonError_nonneg
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ ja b t τ : ℝ)
    (hℓ : 0 ≤ ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hja : 0 ≤ ja) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    0 ≤ propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ B x G e := by
  have hNpos : 0 < N := lt_of_lt_of_le (div_pos hN₀ hc) hN
  have hs : 0 ≤ propensitySignCost Q S x₀ ℓ r h c N N₀ B x G := by
    unfold propensitySignCost
    positivity
  have hg := (propensityGhostDefectSum_bounds Q S x₀ r τ x G e).1
  rw [propensityComparisonError_factor Q S x₀ ℓ r h c N N₀ ja b t τ hja hb ht B x G e]
  unfold propensityPatternScale
  positivity

theorem geometric_defect_square_bound (k g D : ℝ) (hD : 0 ≤ D) (hDk : D ≤ k) :
    (k * g + D) ^ 2 ≤ (2 * k) * (k * g ^ 2 + D) := by
  nlinarith [sq_nonneg (k * g - D), mul_nonneg hD (sub_nonneg.mpr hDk)]

def propensityFineHellingerCoefficient (Q q k D : ℕ) (c N₀ M θ κ : ℝ) : ℝ :=
  (4 : ℝ) ^ q *
    (propensityErrorConstant Q q k D c N₀ M / ((1 - θ) ^ (5 ^ D)) ^ q) ^ 2 /
      (κ ^ 2) ^ q * (2 * k)

theorem propensityFineHellingerCoefficient_nonneg (Q q k D : ℕ) (c N₀ M θ κ : ℝ) :
    0 ≤ propensityFineHellingerCoefficient Q q k D c N₀ M θ κ := by
  unfold propensityFineHellingerCoefficient
  positivity

def propensityLocalFineConstant (Q D : ℕ) (c N₀ M θ κ : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (Q + 1), ∑ k ∈ Finset.range (Q * 5 ^ D + 1),
    propensityFineHellingerCoefficient Q q k D c N₀ M θ κ

theorem propensityLocalFineConstant_nonneg (Q D : ℕ) (c N₀ M θ κ : ℝ) :
    0 ≤ propensityLocalFineConstant Q D c N₀ M θ κ := by
  exact Finset.sum_nonneg (fun q _ => Finset.sum_nonneg
    (fun k _ => propensityFineHellingerCoefficient_nonneg Q q k D c N₀ M θ κ))

theorem propensityFineHellingerCoefficient_le_uniform (Q q k D : ℕ) (c N₀ M θ κ : ℝ)
    (hq : q ≤ Q) (hk : k ≤ Q * 5 ^ D) :
    propensityFineHellingerCoefficient Q q k D c N₀ M θ κ ≤
      propensityLocalFineConstant Q D c N₀ M θ κ := by
  apply (Finset.single_le_sum
    (fun k _ => propensityFineHellingerCoefficient_nonneg Q q k D c N₀ M θ κ)
    (Finset.mem_range.mpr (by omega : k < Q * 5 ^ D + 1))).trans
  exact Finset.single_le_sum
    (fun q _ => Finset.sum_nonneg (fun k _ => propensityFineHellingerCoefficient_nonneg Q q k D c N₀ M θ κ))
    (Finset.mem_range.mpr (by omega : q < Q + 1))

theorem propensityComparisonError_fine_hellinger_bound
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ ja b t τ M θ κ : ℝ)
    (hℓ : 0 ≤ ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hM : 0 ≤ M)
    (hja : 0 ≤ ja) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1) (hB : ∀ k, ‖B k‖ ≤ 2)
    (hsym : ∀ k j, ‖symbolPart j (B k)‖ ≤ M * (ℓ / (2 * r)) ^ Fintype.card d)
    (x : I → d → ℝ) (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    (4 : ℝ) ^ Fintype.card I *
      (propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ B x G e /
        ((1 - θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I) ^ 2 / (κ ^ 2) ^ Fintype.card I ≤
      propensityFineHellingerCoefficient Q (Fintype.card I) (Fintype.card S) (Fintype.card d) c N₀ M θ κ *
        (ja * b * t) ^ 2 * ((Fintype.card S : ℝ) * ((ℓ / (2 * r)) ^ Fintype.card d) ^ 2 +
          propensityGhostDefectSum Q S x₀ r τ x G e) := by
  let E := propensityComparisonError Q S x₀ ℓ r h c N N₀ ja b t τ B x G e
  let C := propensityErrorConstant Q (Fintype.card I) (Fintype.card S) (Fintype.card d) c N₀ M
  let a := ja * b * t
  let k : ℝ := Fintype.card S
  let g := (ℓ / (2 * r)) ^ Fintype.card d
  let D := propensityGhostDefectSum Q S x₀ r τ x G e
  have hE : 0 ≤ E := propensityComparisonError_nonneg Q S x₀ ℓ r h c N N₀ ja b t τ
    hℓ hr hc hN₀ hN hja hb ht B x G e
  have he : E ≤ a * C * (k * g + D) := propensityComparisonError_geometric_bound
    Q S x₀ ℓ r h c N N₀ ja b t τ M hℓ hr hc hN₀ hN hM hja hb ht B hB hsym x G e
  have hD := propensityGhostDefectSum_bounds Q S x₀ r τ x G e
  have hbnd : E ^ 2 ≤ (a * C) ^ 2 * (2 * k) * (k * g ^ 2 + D) := by
    calc
      _ ≤ (a * C * (k * g + D)) ^ 2 := pow_le_pow_left₀ hE he 2
      _ = (a * C) ^ 2 * (k * g + D) ^ 2 := mul_pow _ _ 2
      _ ≤ (a * C) ^ 2 * ((2 * k) * (k * g ^ 2 + D)) :=
        mul_le_mul_of_nonneg_left (geometric_defect_square_bound k g D hD.1 hD.2) (sq_nonneg _)
      _ = _ := by ring
  let W := (4 : ℝ) ^ Fintype.card I /
    (((1 - θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I) ^ 2 / (κ ^ 2) ^ Fintype.card I
  have hW : 0 ≤ W := by dsimp [W]; positivity
  calc
    _ = W * E ^ 2 := by dsimp only [W, E]; rw [div_pow]; ring
    _ ≤ W * ((a * C) ^ 2 * (2 * k) * (k * g ^ 2 + D)) := mul_le_mul_of_nonneg_left hbnd hW
    _ = _ := by
      dsimp only [W, a, C, k, g, D, propensityFineHellingerCoefficient]
      rw [div_pow]
      ring

end CausalLowerbound.PartC

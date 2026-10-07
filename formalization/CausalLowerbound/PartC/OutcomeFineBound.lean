import CausalLowerbound.PartC.OutcomeErrorReduction
import CausalLowerbound.PartC.OutcomeErrorCompletion
import CausalLowerbound.PartC.PropensityFineBound

/-! Square the cubic comparison without squaring the ghost defect, and
choose one finite constant for all small observation components. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def outcomeFineHellingerCoefficient (Q q k D : ℕ) (c N₀ M θ κ : ℝ) : ℝ :=
  (4 : ℝ) ^ q *
    (outcomeErrorConstant Q q k D c N₀ M / ((1 - θ) ^ (5 ^ D)) ^ q) ^ 2 /
      (κ ^ 2) ^ q * (2 * k)

theorem outcomeFineHellingerCoefficient_nonneg (Q q k D : ℕ) (c N₀ M θ κ : ℝ) :
    0 ≤ outcomeFineHellingerCoefficient Q q k D c N₀ M θ κ := by
  unfold outcomeFineHellingerCoefficient
  positivity

def outcomeLocalFineConstant (Q D : ℕ) (c N₀ M θ κ : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (Q + 1), ∑ k ∈ Finset.range (Q * 5 ^ D + 1),
    outcomeFineHellingerCoefficient Q q k D c N₀ M θ κ

theorem outcomeLocalFineConstant_nonneg (Q D : ℕ) (c N₀ M θ κ : ℝ) :
    0 ≤ outcomeLocalFineConstant Q D c N₀ M θ κ := by
  exact Finset.sum_nonneg (fun q _ => Finset.sum_nonneg
    (fun k _ => outcomeFineHellingerCoefficient_nonneg Q q k D c N₀ M θ κ))

theorem outcomeFineHellingerCoefficient_le_uniform (Q q k D : ℕ) (c N₀ M θ κ : ℝ)
    (hq : q ≤ Q) (hk : k ≤ Q * 5 ^ D) :
    outcomeFineHellingerCoefficient Q q k D c N₀ M θ κ ≤
      outcomeLocalFineConstant Q D c N₀ M θ κ := by
  apply (Finset.single_le_sum
    (fun k _ => outcomeFineHellingerCoefficient_nonneg Q q k D c N₀ M θ κ)
    (Finset.mem_range.mpr (by omega : k < Q * 5 ^ D + 1))).trans
  exact Finset.single_le_sum
    (fun q _ => Finset.sum_nonneg (fun k _ => outcomeFineHellingerCoefficient_nonneg Q q k D c N₀ M θ κ))
    (Finset.mem_range.mpr (by omega : q < Q + 1))

theorem outcomeComparisonError_fine_hellinger_bound
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ a jb t τ M θ κ : ℝ)
    (hℓ : 0 ≤ ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hM : 0 ≤ M)
    (hshift : 0 ≤ a * t) (hjb : 0 ≤ jb)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (hB : ∀ k, ‖B k‖ ≤ 2)
    (hsym : ∀ k j, ‖symbolPart j (B k)‖ ≤ M * (ℓ / (2 * r)) ^ Fintype.card d)
    (x : I → d → ℝ) (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    (4 : ℝ) ^ Fintype.card I *
      (outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G e /
        ((1 - θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I) ^ 2 / (κ ^ 2) ^ Fintype.card I ≤
      outcomeFineHellingerCoefficient Q (Fintype.card I) (Fintype.card S) (Fintype.card d) c N₀ M θ κ *
        (a * t * jb) ^ 2 * ((Fintype.card S : ℝ) * ((ℓ / (2 * r)) ^ Fintype.card d) ^ 2 +
          propensityGhostDefectSum Q S x₀ r τ x G e) := by
  let E := outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G e
  let C := outcomeErrorConstant Q (Fintype.card I) (Fintype.card S) (Fintype.card d) c N₀ M
  let target := a * t * jb
  let k : ℝ := Fintype.card S
  let g := (ℓ / (2 * r)) ^ Fintype.card d
  let D := propensityGhostDefectSum Q S x₀ r τ x G e
  have hE : 0 ≤ E := outcomeObservationComparisonError_nonneg Q S x₀ ℓ r h c N N₀ a jb t τ
    hℓ hr.le hc.le ((div_pos hN₀ hc).trans_le hN).le hN₀.le hjb hshift B x G e
  have he : E ≤ target * C * (k * g + D) := outcomeComparisonError_geometric_bound
    Q S x₀ ℓ r h c N N₀ a jb t τ M hℓ hr hc hN₀ hN hM hshift hjb B hB hsym x G e
  have hD := propensityGhostDefectSum_bounds Q S x₀ r τ x G e
  have hbnd : E ^ 2 ≤ (target * C) ^ 2 * (2 * k) * (k * g ^ 2 + D) := by
    calc
      _ ≤ (target * C * (k * g + D)) ^ 2 := pow_le_pow_left₀ hE he 2
      _ = (target * C) ^ 2 * (k * g + D) ^ 2 := mul_pow _ _ 2
      _ ≤ (target * C) ^ 2 * ((2 * k) * (k * g ^ 2 + D)) :=
        mul_le_mul_of_nonneg_left (geometric_defect_square_bound k g D hD.1 hD.2) (sq_nonneg _)
      _ = _ := by ring
  let W := (4 : ℝ) ^ Fintype.card I /
    (((1 - θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I) ^ 2 / (κ ^ 2) ^ Fintype.card I
  have hW : 0 ≤ W := by dsimp [W]; positivity
  calc
    _ = W * E ^ 2 := by dsimp only [W, E]; rw [div_pow]; ring
    _ ≤ W * ((target * C) ^ 2 * (2 * k) * (k * g ^ 2 + D)) := mul_le_mul_of_nonneg_left hbnd hW
    _ = _ := by
      dsimp only [W, target, C, k, g, D, outcomeFineHellingerCoefficient]
      rw [div_pow]
      ring

end CausalLowerbound.PartC

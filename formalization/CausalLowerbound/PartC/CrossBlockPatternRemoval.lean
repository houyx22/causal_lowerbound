import CausalLowerbound.PartC.WeightedPropensityPatterns
import CausalLowerbound.PartC.CrossBlockRemoval
import CausalLowerbound.PartC.SharedSignParity

/-! Cross-block removal for the actual degree-one substitution patterns.
All blocks are included, even those with no selected slots. The common
normalization is absorbed into the selected-slot weights, and reflection
supplies the physical shift-times-rough factor after sign averaging. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Wiener Representative PartB PartB.ShellGeometry
variable {d V J K : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype K]

def propensityPatternProduct (N : ℝ) (κ : K → V → ℝ) (W : K → Array d V J 1)
    (u : K → V × d → ℝ) (z : K → V → ℝ) (ζ : J → Bool) (A : K → Finset V) : ℝ :=
  ∏ k, weightedPropensityPatternWeight N (κ k) (W k) (u k) (z k) ζ (A k)

theorem propensityPatternProduct_amplitude (amp N : ℝ) (κ : K → V → ℝ) (W : K → Array d V J 1)
    (u : K → V × d → ℝ) (z : K → V → ℝ) (ζ : J → Bool) (A : K → Finset V) :
    (∏ k, (amp * N) ^ (A k).card * propensityPatternWeight (κ k) (W k) (u k) (z k) ζ (A k)) =
      amp ^ (∑ k, (A k).card) * propensityPatternProduct N κ W u z ζ A := by
  simp only [weightedPropensityPatternWeight_amplitude, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, propensityPatternProduct]

theorem propensityPatternProduct_reflection_fixed (N : ℝ) (κ : K → V → ℝ)
    (W : K → Array d V J 1) (hW : ∀ k, reflection (W k) = W k)
    (u : K → V × d → ℝ) (z : (J → Bool) → K → V → ℝ)
    (hz : ∀ ζ k i, z (Walsh.flip ζ) k i = -z ζ k i) (ζ : J → Bool) (A : K → Finset V) :
    propensityPatternProduct N κ W u (z (Walsh.flip ζ)) (Walsh.flip ζ) A =
      (-1) ^ (∑ k, (A k).card) * propensityPatternProduct N κ W u (z ζ) ζ A := by
  unfold propensityPatternProduct
  simp_rw [weightedPropensityPatternWeight_reflection_fixed N _ _ (hW _) _
    (fun ζ => z ζ _) (fun ζ i => hz ζ _ i)]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem propensityPatternProduct_removal_parity (N : ℝ) (κ : K → V → ℝ)
    (W : K → Array d V J 1) (hW : ∀ k, reflection (W k) = W k)
    (u : K → V × d → ℝ) (z : (J → Bool) → K → V → ℝ)
    (hz : ∀ ζ k i, z (Walsh.flip ζ) k i = -z ζ k i) (S : Finset J)
    (ζ : J → Bool) (A : K → Finset V) :
    propensityPatternProduct N κ W u (z (Walsh.flip ζ)) (Walsh.flip ζ) A -
      propensityPatternProduct N κ (fun k => remove S (W k)) u (z (Walsh.flip ζ)) (Walsh.flip ζ) A =
      (-1) ^ (∑ k, (A k).card) * (propensityPatternProduct N κ W u (z ζ) ζ A -
        propensityPatternProduct N κ (fun k => remove S (W k)) u (z ζ) ζ A) := by
  rw [propensityPatternProduct_reflection_fixed N κ W hW u z hz,
    propensityPatternProduct_reflection_fixed N κ (fun k => remove S (W k))
      (fun k => reflection_remove_of_fixed S (W k) (hW k)) u z hz, mul_sub]

theorem propensityPatternProduct_removal_bound (N : ℝ) (κ : K → V → ℝ)
    (W : K → Array d V J 1) (u : K → V × d → ℝ) (z : K → V → ℝ)
    (ζ : J → Bool) (A : K → Finset V) (S : Finset J) (C : ℝ) (hC : 1 ≤ C)
    (hW : ∀ k, ‖W k‖ ≤ 2) (hz : ∀ k i, |z k i| ≤ 1)
    (hNz : ∀ k i, |N * z k i| ≤ C) (hNκ : ∀ k i, |N * κ k i| ≤ C) :
    |propensityPatternProduct N κ W u z ζ A -
      propensityPatternProduct N κ (fun k => remove S (W k)) u z ζ A| ≤
      (2 * C ^ Fintype.card V) ^ Fintype.card K * C ^ Fintype.card V *
        ∑ k, ∑ j ∈ S, ‖symbolPart j (W k)‖ := by
  let L := C ^ Fintype.card V
  have hL : 1 ≤ L := one_le_pow₀ hC
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hb (k : K) (B : Array d V J 1) :
      |weightedPropensityPatternWeight N (κ k) B (u k) (z k) ζ (A k)| ≤ L * ‖B‖ :=
    weightedPropensityPatternWeight_bound N (κ k) B (u k) (z k) ζ (A k) C hC (hz k) (hNz k) (hNκ k)
  have hd (k : K) :
      |weightedPropensityPatternWeight N (κ k) (W k) (u k) (z k) ζ (A k) -
        weightedPropensityPatternWeight N (κ k) (remove S (W k)) (u k) (z k) ζ (A k)| ≤
        L * ∑ j ∈ S, ‖symbolPart j (W k)‖ := by
    rw [← weightedPropensityPatternWeight_sub]
    exact (hb k (W k - remove S (W k))).trans (mul_le_mul_of_nonneg_left (removal_error S (W k)) hL0)
  have hf (k : K) : |weightedPropensityPatternWeight N (κ k) (W k) (u k) (z k) ζ (A k)| ≤ 2 * L :=
    (hb k (W k)).trans ((mul_le_mul_of_nonneg_left (hW k) hL0).trans_eq (mul_comm L 2))
  have hg (k : K) : |weightedPropensityPatternWeight N (κ k) (remove S (W k)) (u k) (z k) ζ (A k)| ≤ 2 * L :=
    (hb k (remove S (W k))).trans
      ((mul_le_mul_of_nonneg_left ((remove_bound S (W k)).trans (hW k)) hL0).trans_eq (mul_comm L 2))
  apply (abs_prod_sub_prod_le_bounded Finset.univ
    (fun k => weightedPropensityPatternWeight N (κ k) (W k) (u k) (z k) ζ (A k))
    (fun k => weightedPropensityPatternWeight N (κ k) (remove S (W k)) (u k) (z k) ζ (A k))
    (2 * L) (by linarith) (fun k _ => hf k) (fun k _ => hg k)).trans
  simp only [Finset.card_univ]
  calc
    _ ≤ (2 * L) ^ Fintype.card K * ∑ k, L * ∑ j ∈ S, ‖symbolPart j (W k)‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hd k)) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; dsimp only [L]; ring

variable {P I : Type*} [Fintype P] [DecidableEq P] [Fintype I] [DecidableEq d]

theorem physical_pattern_product_removal_bound (N : ℝ) (κ : K → V → ℝ)
    (x₀ : d → ℝ) (ℓ h : ℝ) (sites : P → d → ℝ)
    (W : K → Array d V (activeBlocks (d := d) ℓ h) 1) (u : K → V × d → ℝ)
    (z : K → V → ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool) (A : K → Finset V)
    (C η : ℝ) (hC : 1 ≤ C) (hη : 0 ≤ η) (hW : ∀ k, ‖W k‖ ≤ 2)
    (hsymbol : ∀ k j, ‖symbolPart j (W k)‖ ≤ η)
    (hz : ∀ k i, |z k i| ≤ 1) (hNz : ∀ k i, |N * z k i| ≤ C) (hNκ : ∀ k i, |N * κ k i| ≤ C) :
    let S := Finset.univ.biUnion (fun p => physicalLocalSigns x₀ ℓ h (sites p))
    |propensityPatternProduct N κ W u z ζ A -
      propensityPatternProduct N κ (fun k => remove S (W k)) u z ζ A| ≤
      (2 * C ^ Fintype.card V) ^ Fintype.card K * C ^ Fintype.card V * Fintype.card K *
        ((Fintype.card P : ℝ) * 2 ^ Fintype.card d * η) := by
  dsimp only
  let S := Finset.univ.biUnion (fun p => physicalLocalSigns x₀ ℓ h (sites p))
  have hb (k : K) : (∑ j ∈ S, ‖symbolPart j (W k)‖) ≤ (Fintype.card P : ℝ) * 2 ^ Fintype.card d * η := by
    calc
      _ ≤ ∑ _j ∈ S, η := Finset.sum_le_sum (fun j _ => hsymbol k j)
      _ = (S.card : ℝ) * η := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast physicalLocalSigns_union_card x₀ ℓ h sites) hη
  apply (propensityPatternProduct_removal_bound N κ W u z ζ A S C hC hW hz hNz hNκ).trans
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have he := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hb k))
    (show 0 ≤ (2 * C ^ Fintype.card V) ^ Fintype.card K * C ^ Fintype.card V by positivity)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using he

theorem physical_pattern_shift_removal_bound (N : ℝ) (κ : K → V → ℝ)
    (x₀ : d → ℝ) (ℓ h : ℝ) (sites : P → d → ℝ)
    (W : K → Array d V (activeBlocks (d := d) ℓ h) 1) (u : K → V × d → ℝ)
    (z : (activeBlocks (d := d) ℓ h → Bool) → K → V → ℝ) (A : K → Finset V)
    (hA : 0 < ∑ k, (A k).card)
    (C η shift rough : ℝ) (hC : 1 ≤ C) (hη : 0 ≤ η)
    (hshift : 0 ≤ shift) (hrough : 0 ≤ rough) (hr1 : rough ≤ 1) (hsr : shift ≤ rough)
    (hW : ∀ k, ‖W k‖ ≤ 2) (hreflect : ∀ k, reflection (W k) = W k)
    (hsymbol : ∀ k j, ‖symbolPart j (W k)‖ ≤ η)
    (hz : ∀ ζ k i, |z ζ k i| ≤ 1) (hNz : ∀ ζ k i, |N * z ζ k i| ≤ C)
    (hNκ : ∀ k i, |N * κ k i| ≤ C) (hflip : ∀ ζ k i, z (Walsh.flip ζ) k i = -z ζ k i)
    (f : I → (activeBlocks (d := d) ℓ h → Bool) → ℝ) (hf : ∀ i ζ, |f i ζ| ≤ rough) :
    let S := Finset.univ.biUnion (fun p => physicalLocalSigns x₀ ℓ h (sites p))
    let B := (2 * C ^ Fintype.card V) ^ Fintype.card K * C ^ Fintype.card V * Fintype.card K *
      ((Fintype.card P : ℝ) * 2 ^ Fintype.card d * η)
    |independentSigns.expect (fun ζ => shift ^ (∑ k, (A k).card) *
      (propensityPatternProduct N κ W u (z ζ) ζ A -
        propensityPatternProduct N κ (fun k => remove S (W k)) u (z ζ) ζ A) *
          ∏ i, (1 + f i ζ))| ≤ B * (2 : ℝ) ^ Fintype.card I *
            ((Fintype.card I : ℝ) + 1) * (shift * rough) := by
  dsimp only
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  apply parity_weighted_shift_bound _ hA _
    (fun ζ => propensityPatternProduct_removal_parity N κ W hreflect u z hflip _ ζ A)
    f _ shift rough (by positivity) hshift hrough hr1 hsr _ hf
  intro ζ
  exact physical_pattern_product_removal_bound N κ x₀ ℓ h sites W u (z ζ) ζ A C η hC hη hW hsymbol
    (hz ζ) (hNz ζ) hNκ

end CausalLowerbound.PartC

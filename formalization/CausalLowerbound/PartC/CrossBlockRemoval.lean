import CausalLowerbound.PartC.PhysicalLocalPropensityMatching
import CausalLowerbound.PartC.PhysicalRepresentativeReflection
import CausalLowerbound.FiniteProductBounds

/-! Simultaneous removal of local Walsh symbols from every incident
carrier. The estimates use the original shared sign configuration and
do not assume independence of blocks or positivity of removed factors.
Removal also preserves the reflection used by the parity argument. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC.Representative
open Wiener
variable {d V J K : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype K] {D : ℕ}

theorem remove_union (S T : Finset J) (W : Array d V J D) :
    remove S (remove T W) = remove (S ∪ T) W := by
  apply lp.ext
  funext r
  simp only [remove_apply, Finset.disjoint_union_right]
  by_cases hS : Disjoint r.2 S <;> by_cases hT : Disjoint r.2 T <;> simp [hS, hT]

theorem remove_reflection (S : Finset J) (W : Array d V J D) :
    remove S (reflection W) = reflection (remove S W) := by
  apply lp.ext
  funext r
  simp only [remove_apply, reflection_apply]
  split_ifs <;> simp

theorem reflection_remove_of_fixed (S : Finset J) (W : Array d V J D)
    (hW : reflection W = W) : reflection (remove S W) = remove S W := by
  rw [← remove_reflection, hW]

theorem pointValue_remove_error (S : Finset J) (W : Array d V J D)
    (x : Torus (V × d)) (z : V → ℝ) (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool) :
    |pointValue x z ζ W - pointValue x z ζ (remove S W)| ≤ ∑ j ∈ S, ‖symbolPart j W‖ := by
  have hb := (pointValue_bound x z hz ζ (W - remove S W)).trans (removal_error S W)
  have he := (pointEvaluation x z hz ζ).map_sub W (remove S W)
  simpa only [pointEvaluation_apply] using he ▸ hb

theorem product_remove_error (S : Finset J) (W : K → Array d V J D)
    (x : K → Torus (V × d)) (z : K → V → ℝ) (hz : ∀ k i, |z k i| ≤ 1)
    (ζ : J → Bool) (M : ℝ) (hM : 1 ≤ M) (hW : ∀ k, ‖W k‖ ≤ M) :
    |(∏ k, pointValue (x k) (z k) ζ (W k)) -
      ∏ k, pointValue (x k) (z k) ζ (remove S (W k))| ≤
      M ^ Fintype.card K * ∑ k, ∑ j ∈ S, ‖symbolPart j (W k)‖ := by
  have he := abs_prod_sub_prod_le_bounded Finset.univ
    (fun k => pointValue (x k) (z k) ζ (W k))
    (fun k => pointValue (x k) (z k) ζ (remove S (W k))) M hM
    (fun k _ => (pointValue_bound (x k) (z k) (hz k) ζ (W k)).trans (hW k))
    (fun k _ => (pointValue_bound (x k) (z k) (hz k) ζ (remove S (W k))).trans
      ((remove_bound S (W k)).trans (hW k)))
  apply he.trans
  simp only [Finset.card_univ]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hM) _)
  exact Finset.sum_le_sum (fun k _ => pointValue_remove_error S (W k) (x k) (z k) (hz k) ζ)

end CausalLowerbound.PartC.Representative

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative
variable {d V I K : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype K] {D : ℕ}

theorem physical_cross_block_removal_bound (x₀ : d → ℝ) (ℓ h : ℝ) (sites : I → d → ℝ)
    (W : K → Array d V (activeBlocks (d := d) ℓ h) D)
    (x : K → Torus (V × d)) (z : K → V → ℝ) (hz : ∀ k i, |z k i| ≤ 1)
    (ζ : activeBlocks (d := d) ℓ h → Bool)
    (C : ℝ) (hC : 0 ≤ C) (hW : ∀ k, ‖W k‖ ≤ 2) (hsymbol : ∀ k j, ‖symbolPart j (W k)‖ ≤ C) :
    let S := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (sites i))
    |(∏ k, pointValue (x k) (z k) ζ (W k)) -
      ∏ k, pointValue (x k) (z k) ζ (remove S (W k))| ≤
      (2 : ℝ) ^ Fintype.card K * Fintype.card K *
        ((Fintype.card I : ℝ) * 2 ^ Fintype.card d * C) := by
  dsimp only
  let S := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (sites i))
  have hb (k : K) : (∑ j ∈ S, ‖symbolPart j (W k)‖) ≤ (Fintype.card I : ℝ) * 2 ^ Fintype.card d * C := by
    calc
      _ ≤ ∑ _j ∈ S, C := Finset.sum_le_sum (fun j _ => hsymbol k j)
      _ = (S.card : ℝ) * C := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast physicalLocalSigns_union_card x₀ ℓ h sites) hC
  apply (product_remove_error S W x z hz ζ 2 (by norm_num) hW).trans
  have he := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hb k))
    (show 0 ≤ (2 : ℝ) ^ Fintype.card K by positivity)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using he

theorem physical_removed_carrier_product_flip (x₀ : d → ℝ) (ℓ h : ℝ)
    (r : K → ℝ) (k : K → d → ℤ) (c w N : ℝ)
    (W : K → Array d V (activeBlocks (d := d) ℓ h) D) (hW : ∀ a, reflection (W a) = W a)
    (S : Finset (activeBlocks (d := d) ℓ h)) (u : K → V × d → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    (∏ a, pointValue (torusProjection (u a))
      (fun i => normalizedRoughChart x₀ ℓ (r a) h (k a) c w N (Walsh.flip ζ) (configurationSite (u a) i))
      (Walsh.flip ζ) (remove S (W a))) =
    ∏ a, pointValue (torusProjection (u a))
      (fun i => normalizedRoughChart x₀ ℓ (r a) h (k a) c w N ζ (configurationSite (u a) i))
      ζ (remove S (W a)) := by
  apply Finset.prod_congr rfl
  intro a _
  have he := physical_pointValue_reflection x₀ ℓ (r a) h (k a) c w N ζ (u a) (remove S (W a))
  rw [reflection_remove_of_fixed S (W a) (hW a)] at he
  exact he.symm

end CausalLowerbound.PartC

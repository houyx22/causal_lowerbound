import CausalLowerbound.PartC.CarrierDesignMarginals
import CausalLowerbound.PartB.GlobalGhostCost

/-! Integrate the unweighted ghost majorant under the actual Part C
mixed design. Coordinate domination controls the retained observations;
the finite subset and block counts give the required n h^d τ^s bound. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d K J Ω U V : Type*} [Fintype d] [DecidableEq d]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype Ω]
  [Fintype U] [Fintype V] {θ : ℝ}

theorem mixedCarrierDesign_physicalGhostCost_zero_le [Nonempty d]
    (H₀ : DiscreteLaw ℕ) (q : ℕ) (e : U ⊕ V ≃ Fin (q + 1))
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (τ : ℝ) (hτ : 0 < τ)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (k : d → ℤ) (n : ℕ) (v : U → Fin n) (hv : Function.Injective v) :
    (∫ x, physicalGhostCost H₀ (q + 1) e 0 τ x₀ r k (fun i => x (v i))
      ∂mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) ≤
      ghostSubsetBound d q θ s τ r (Fintype.card U) := by
  obtain ⟨hm, hi, h0⟩ := physicalGhostCost_regular H₀ (q + 1) e 0 τ
    (by norm_num) (by norm_num) x₀ r hr k
  have hb := mixedCarrierDesign_coordinate_integral_le F hθ hθ1 S x₀ r H kernel n v hv
    (physicalGhostCost H₀ (q + 1) e 0 τ x₀ r k) hm h0 hi
  let A := (q + 1 : ℝ) * ((2 * τ) ^ s * collisionMomentBound d s ^ q)
  have hA : 0 ≤ A := by
    dsimp [A]
    have hM := collisionMomentBound_nonneg (d := d) s
    positivity
  have hd : 0 < (1 - θ) ^ Fintype.card U := pow_pos (by linarith) _
  have hd1 : (1 - θ) ^ Fintype.card U ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hn1 : 1 ≤ (1 + θ) ^ (q + 1) := one_le_pow₀ (by linarith)
  have hf : A ≤ (1 + θ) ^ (q + 1) * A / (1 - θ) ^ Fintype.card U := by
    apply (le_div_iff₀ hd).mpr
    exact (mul_le_of_le_one_right hA hd1).trans (le_mul_of_one_le_left hA hn1)
  apply hb.trans
  unfold ghostSubsetBound
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [physicalGhostCost, integral_indicator (carrierConfigurationBox_measurable x₀ r k)]
  have hp : (∫ x in carrierConfigurationBox (K := U) x₀ r k,
      1 - ghostActivation H₀ (q + 1) 0 (completedTorusTaper (q + 1) e τ)
        (fun i => Wiener.torusProjection (carrierCoordinate (localCoordinate x₀ r k (x i))))) ≤
        (4 * r) ^ (Fintype.card U * Fintype.card d) * A := by
    simpa only [add_zero, sub_zero, one_pow, one_mul, div_one, A] using
      physical_ghost_leakage H₀ q e 0 (by norm_num) (by norm_num) s hs hsd τ hτ x₀ r hr k
  exact hp.trans (mul_le_mul_of_nonneg_left hf (by positivity))

theorem mixedCarrierDesign_blockSubsetCost_integrable
    (H₀ : DiscreteLaw ℕ) (Q : ℕ) (τ : ℝ)
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (k : d → ℤ) {n : ℕ} (T : Finset (Fin n)) (hT : T.card ≤ Q) :
    Integrable (blockSubsetCost H₀ Q 0 τ x₀ r k T hT)
      (mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) := by
  exact mixedCarrierDesign_coordinate_integrable F hθ hθ1 S x₀ r H kernel n Subtype.val
    Subtype.val_injective _
    (physicalGhostCost_regular H₀ Q (siteCompletion Q T hT) 0 τ
      (by norm_num) (by norm_num) x₀ r hr k).2.1

theorem mixedCarrierDesign_smallBlockCost_integrable
    (H₀ : DiscreteLaw ℕ) (Q : ℕ) (τ : ℝ)
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (k : d → ℤ) (n : ℕ) :
    Integrable (fun x : Fin n → d → ℝ => smallBlockCost H₀ Q 0 τ x₀ r k x)
      (mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) := by
  exact integrable_finset_sum _ (fun q _ => integrable_finset_sum _ (fun T _ =>
    mixedCarrierDesign_blockSubsetCost_integrable H₀ Q τ F hθ hθ1 S x₀ r hr H kernel k
      T.val (powersetCard_small q T)))

theorem mixedCarrierDesign_smallBlockCost_integral_le [Nonempty d]
    (H₀ : DiscreteLaw ℕ) (q : ℕ)
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (τ : ℝ) (hτ : 0 < τ)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (k : d → ℤ) (n : ℕ) :
    (∫ x : Fin n → d → ℝ, smallBlockCost H₀ (q + 1) 0 τ x₀ r k x
      ∂mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) ≤
      ∑ j : Fin (q + 1), (n : ℝ) ^ (j.val + 1) * ghostSubsetBound d q θ s τ r (j.val + 1) := by
  unfold smallBlockCost
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun T _ =>
    mixedCarrierDesign_blockSubsetCost_integrable H₀ (q + 1) τ F hθ hθ1 S x₀ r hr H kernel k
      T.val (powersetCard_small j T)))]
  apply Finset.sum_le_sum
  intro j _
  rw [integral_finset_sum _ (fun T _ =>
    mixedCarrierDesign_blockSubsetCost_integrable H₀ (q + 1) τ F hθ hθ1 S x₀ r hr H kernel k
      T.val (powersetCard_small j T))]
  have hb (T : (Finset.univ : Finset (Fin n)).powersetCard (j.val + 1)) :
      (∫ x, blockSubsetCost H₀ (q + 1) 0 τ x₀ r k T.val (powersetCard_small j T) x
        ∂mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) ≤
          ghostSubsetBound d q θ s τ r (j.val + 1) := by
    have hh := mixedCarrierDesign_physicalGhostCost_zero_le H₀ q
      (siteCompletion (q + 1) T.val (powersetCard_small j T)) F hθ hθ1
      s hs hsd τ hτ S x₀ r hr H kernel k n Subtype.val Subtype.val_injective
    simpa only [blockSubsetCost, Fintype.card_coe, (Finset.mem_powersetCard.mp T.property).2] using hh
  calc
    _ ≤ ∑ _ : (Finset.univ : Finset (Fin n)).powersetCard (j.val + 1),
        ghostSubsetBound d q θ s τ r (j.val + 1) := Finset.sum_le_sum (fun T _ => hb T)
    _ = (n.choose (j.val + 1) : ℝ) * ghostSubsetBound d q θ s τ r (j.val + 1) := by simp
    _ ≤ (n : ℝ) ^ (j.val + 1) * ghostSubsetBound d q θ s τ r (j.val + 1) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow n (j.val + 1))
        (ghostSubsetBound_nonneg q θ s τ r hθ hθ1 hr.le hτ.le _)

theorem mixedCarrierDesign_smallBlockCost_integral_sparse [Nonempty d]
    (H₀ : DiscreteLaw ℕ) (q : ℕ)
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (τ : ℝ) (hτ : 0 < τ)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (k : d → ℤ) (n : ℕ) (hnr : (n : ℝ) * r ^ Fintype.card d ≤ 1) :
    (∫ x : Fin n → d → ℝ, smallBlockCost H₀ (q + 1) 0 τ x₀ r k x
      ∂mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) ≤
      (∑ j : Fin (q + 1), ghostSubsetCoefficient d q θ s (j.val + 1)) *
        ((n : ℝ) * r ^ Fintype.card d * τ ^ s) := by
  apply (mixedCarrierDesign_smallBlockCost_integral_le H₀ q F hθ hθ1 s hs hsd τ hτ
    S x₀ r hr H kernel k n).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hp : ((n : ℝ) * r ^ Fintype.card d) ^ (j.val + 1) ≤ (n : ℝ) * r ^ Fintype.card d := by
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (by positivity) hnr) (by positivity)).trans_eq (one_mul _)
  have he : (n : ℝ) ^ (j.val + 1) * ghostSubsetBound d q θ s τ r (j.val + 1) =
      ghostSubsetCoefficient d q θ s (j.val + 1) * τ ^ s *
        ((n : ℝ) * r ^ Fintype.card d) ^ (j.val + 1) := by
    rw [ghostSubsetBound_factor q θ s τ r hτ.le, mul_pow, ← pow_mul,
      Nat.mul_comm (Fintype.card d) (j.val + 1)]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg
    (ghostSubsetCoefficient_nonneg (d := d) q θ s hθ hθ1 (j.val + 1)) (Real.rpow_nonneg hτ.le s))
  convert hh using 1 <;> ring

theorem mixedCarrierDesign_globalGhostCost_integrable
    (H₀ : DiscreteLaw ℕ) (Q : ℕ) (τ : ℝ)
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) :
    Integrable (fun x : Fin n → d → ℝ => globalGhostCost H₀ Q 0 τ x₀ r h x)
      (mixedCarrierDesign F hθ hθ1 (activeBlocks r h) x₀ r H kernel n) := by
  exact integrable_finset_sum _ (fun k _ => mixedCarrierDesign_smallBlockCost_integrable
    H₀ Q τ F hθ hθ1 (activeBlocks r h) x₀ r hr H kernel k.val n)

theorem mixedCarrierDesign_globalGhostCost_integral_le [Nonempty d]
    (H₀ : DiscreteLaw ℕ) (q : ℕ)
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (τ : ℝ) (hτ : 0 < τ)
    (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hrh : r ≤ h)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (n : ℕ) (hnr : (n : ℝ) * r ^ Fintype.card d ≤ 1) :
    (∫ x : Fin n → d → ℝ, globalGhostCost H₀ (q + 1) 0 τ x₀ r h x
      ∂mixedCarrierDesign F hθ hθ1 (activeBlocks r h) x₀ r H kernel n) ≤
      globalGhostConstant d q θ s * ((n : ℝ) * h ^ Fintype.card d * τ ^ s) := by
  let C := ∑ j : Fin (q + 1), ghostSubsetCoefficient d q θ s (j.val + 1)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => ghostSubsetCoefficient_nonneg q θ s hθ hθ1 _)
  unfold globalGhostCost
  rw [integral_finset_sum _ (fun k _ => mixedCarrierDesign_smallBlockCost_integrable
    H₀ (q + 1) τ F hθ hθ1 (activeBlocks r h) x₀ r hr H kernel k.val n)]
  calc
    _ ≤ ∑ _ : activeBlocks (d := d) r h, C * ((n : ℝ) * r ^ Fintype.card d * τ ^ s) :=
      Finset.sum_le_sum (fun k _ => mixedCarrierDesign_smallBlockCost_integral_sparse
        H₀ q F hθ hθ1 s hs hsd τ hτ (activeBlocks r h) x₀ r hr H kernel k.val n hnr)
    _ = ((activeBlocks (d := d) r h).card : ℝ) * (C * ((n : ℝ) * r ^ Fintype.card d * τ ^ s)) := by simp
    _ ≤ (7 * (h / r)) ^ Fintype.card d * (C * ((n : ℝ) * r ^ Fintype.card d * τ ^ s)) :=
      mul_le_mul_of_nonneg_right (activeBlocks_card_bound r h hr hrh) (by positivity)
    _ = globalGhostConstant d q θ s * ((n : ℝ) * h ^ Fintype.card d * τ ^ s) := by
      unfold globalGhostConstant
      dsimp only [C]
      rw [mul_pow, div_pow]
      field_simp
      ring

end CausalLowerbound.PartC

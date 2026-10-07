import CausalLowerbound.PartB.MixedGhostLeakage
import CausalLowerbound.PartB.PhysicalActivation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds

/-! A measurable majorant for the sum of leakage costs. Enumerating
nonempty observed subsets removes the random carrier-site index from
the integration step. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

def blockSubsetCost (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ) (x₀ : d → ℝ)
    (r : ℝ) (k : d → ℤ) {n : ℕ} (T : Finset (Fin n)) (hT : T.card ≤ Q) :
    (Fin n → d → ℝ) → ℝ :=
  fun x => physicalGhostCost H Q (siteCompletion Q T hT) θ t x₀ r k (fun i : T => x i.val)

theorem blockSubsetCost_regular (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ)
    {n : ℕ} (T : Finset (Fin n)) (hT : T.card ≤ Q) :
    Measurable (blockSubsetCost H Q θ t x₀ r k T hT) ∧
      ∀ x, 0 ≤ blockSubsetCost H Q θ t x₀ r k T hT x := by
  have hh := physicalGhostCost_regular H Q (siteCompletion Q T hT) θ t hθ hθ1 x₀ r hr k
  exact ⟨hh.1.comp (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)),
    fun x => hh.2.2 _⟩

theorem blockSubsetCost_integrable (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : Finset (d → ℤ)) (kernel : ℕ → FiniteLaw Ω)
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ)
    {n : ℕ} (T : Finset (Fin n)) (hT : T.card ≤ Q) :
    Integrable (blockSubsetCost H Q θ t x₀ r k T hT)
      (mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n) := by
  exact mixedDesign_coordinate_integrable Q S θ hθ hθ1 H kernel x₀ r n Subtype.val
    Subtype.val_injective _
      (physicalGhostCost_regular H Q (siteCompletion Q T hT) θ t hθ hθ1 x₀ r hr k).2.1

theorem blockSubsetCost_at_carrierSites (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ)
    (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) {n : ℕ} (x : Fin n → d → ℝ)
    (hq : (carrierSites x₀ r k x).card ≤ Q) :
    blockSubsetCost H Q θ t x₀ r k (carrierSites x₀ r k x) hq x =
      1 - evaluatedBlockWeight H Q θ t (carrierSites x₀ r k x)
        (siteCompletion Q _ hq) (physicalBlockCoordinates x₀ r x k) := by
  have hm : (fun i : carrierSites x₀ r k x => x i.val) ∈
      carrierConfigurationBox x₀ r k := by
    intro i _
    exact (Finset.mem_filter.mp i.property).2
  rw [blockSubsetCost, physicalGhostCost, Set.indicator_of_mem hm]
  rfl

theorem powersetCard_small {n Q : ℕ} (q : Fin Q)
    (T : (Finset.univ : Finset (Fin n)).powersetCard (q.val + 1)) : T.val.card ≤ Q := by
  have hh := (Finset.mem_powersetCard.mp T.property).2
  have hq := q.isLt
  omega

def smallBlockCost (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ) (x₀ : d → ℝ)
    (r : ℝ) (k : d → ℤ) {n : ℕ} (x : Fin n → d → ℝ) : ℝ :=
  ∑ q : Fin Q, ∑ T : (Finset.univ : Finset (Fin n)).powersetCard (q.val + 1),
    blockSubsetCost H Q θ t x₀ r k T.val (powersetCard_small q T) x

theorem smallBlockCost_nonneg (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ)
    {n : ℕ} (x : Fin n → d → ℝ) : 0 ≤ smallBlockCost H Q θ t x₀ r k x := by
  exact Finset.sum_nonneg (fun q _ => Finset.sum_nonneg (fun T _ =>
    (blockSubsetCost_regular H Q θ t hθ hθ1 x₀ r hr k T.val (powersetCard_small q T)).2 x))

theorem smallBlockCost_measurable (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ) (n : ℕ) :
    Measurable (fun x : Fin n → d → ℝ => smallBlockCost H Q θ t x₀ r k x) := by
  exact Finset.measurable_sum _ (fun q _ => Finset.measurable_sum _ (fun T _ =>
    (blockSubsetCost_regular H Q θ t hθ hθ1 x₀ r hr k T.val (powersetCard_small q T)).1))

theorem smallBlockCost_integrable (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : Finset (d → ℤ)) (kernel : ℕ → FiniteLaw Ω)
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ) (n : ℕ) :
    Integrable (fun x : Fin n → d → ℝ => smallBlockCost H Q θ t x₀ r k x)
      (mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n) := by
  exact integrable_finset_sum _ (fun q _ => integrable_finset_sum _ (fun T _ =>
    blockSubsetCost_integrable H Q θ t hθ hθ1 S kernel x₀ r hr k T.val (powersetCard_small q T)))

theorem actual_block_leakage_le_smallBlockCost (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ)
    {n : ℕ} (x : Fin n → d → ℝ) (hq : (carrierSites x₀ r k x).card ≤ Q) :
    (if (carrierSites x₀ r k x).Nonempty then
      1 - evaluatedBlockWeight H Q θ t (carrierSites x₀ r k x)
        (siteCompletion Q _ hq) (physicalBlockCoordinates x₀ r x k) else 0) ≤
      smallBlockCost H Q θ t x₀ r k x := by
  by_cases hne : (carrierSites x₀ r k x).Nonempty
  · rw [if_pos hne, ← blockSubsetCost_at_carrierSites H Q θ t x₀ r k x hq]
    let j : Fin Q := ⟨(carrierSites x₀ r k x).card - 1, by
      have hh := Finset.card_pos.mpr hne
      omega⟩
    have hj : (carrierSites x₀ r k x).card = j.val + 1 := by
      have hh := Finset.card_pos.mpr hne
      dsimp [j]
      omega
    let T : (Finset.univ : Finset (Fin n)).powersetCard (j.val + 1) :=
      ⟨carrierSites x₀ r k x, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hj⟩⟩
    calc
      _ ≤ ∑ U : (Finset.univ : Finset (Fin n)).powersetCard (j.val + 1),
          blockSubsetCost H Q θ t x₀ r k U.val (powersetCard_small j U) x := by
        exact Finset.single_le_sum (fun U _ =>
          (blockSubsetCost_regular H Q θ t hθ hθ1 x₀ r hr k U.val (powersetCard_small j U)).2 x)
          (Finset.mem_univ T)
      _ ≤ smallBlockCost H Q θ t x₀ r k x := by
        unfold smallBlockCost
        apply Finset.single_le_sum (f := fun i : Fin Q =>
          ∑ U : (Finset.univ : Finset (Fin n)).powersetCard (i.val + 1),
            blockSubsetCost H Q θ t x₀ r k U.val (powersetCard_small i U) x) _ (Finset.mem_univ j)
        intro i _
        exact Finset.sum_nonneg (fun U _ =>
          (blockSubsetCost_regular H Q θ t hθ hθ1 x₀ r hr k U.val (powersetCard_small i U)).2 x)
  · rw [if_neg hne]
    exact smallBlockCost_nonneg H Q θ t hθ hθ1 x₀ r hr k x

def ghostSubsetBound (d : Type*) [Fintype d] (q : ℕ) (θ s t r : ℝ) (m : ℕ) : ℝ :=
  (designDensityCeiling d θ : ℝ) ^ m * ((4 * r) ^ (m * Fintype.card d) *
    (((1 + θ) ^ (q + 1) * ((q + 1 : ℝ) * ((2 * t) ^ s * collisionMomentBound d s ^ q))) /
      (1 - θ) ^ m))

theorem ghostSubsetBound_nonneg (q : ℕ) (θ s t r : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (m : ℕ) : 0 ≤ ghostSubsetBound d q θ s t r m := by
  have hM := collisionMomentBound_nonneg (d := d) s
  have hc : 0 ≤ 1 - θ := by linarith
  unfold ghostSubsetBound
  positivity

theorem smallBlockCost_integral_le [Nonempty d] (H : DiscreteLaw ℕ) (q : ℕ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (t : ℝ) (ht : 0 < t)
    (S : Finset (d → ℤ)) (kernel : ℕ → FiniteLaw Ω) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r)
    (k : d → ℤ) (n : ℕ) :
    (∫ x : Fin n → d → ℝ, smallBlockCost H (q + 1) θ t x₀ r k x
      ∂mixedDesignExperiment (q + 1) S θ hθ hθ1 H kernel x₀ r n) ≤
      ∑ j : Fin (q + 1), (n : ℝ) ^ (j.val + 1) * ghostSubsetBound d q θ s t r (j.val + 1) := by
  unfold smallBlockCost
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun T _ =>
    blockSubsetCost_integrable H (q + 1) θ t hθ hθ1 S kernel x₀ r hr k T.val (powersetCard_small j T)))]
  apply Finset.sum_le_sum
  intro j _
  rw [integral_finset_sum _ (fun T _ =>
    blockSubsetCost_integrable H (q + 1) θ t hθ hθ1 S kernel x₀ r hr k T.val (powersetCard_small j T))]
  have hb (T : (Finset.univ : Finset (Fin n)).powersetCard (j.val + 1)) :
      (∫ x, blockSubsetCost H (q + 1) θ t x₀ r k T.val (powersetCard_small j T) x
        ∂mixedDesignExperiment (q + 1) S θ hθ hθ1 H kernel x₀ r n) ≤
          ghostSubsetBound d q θ s t r (j.val + 1) := by
    have hh := mixedDesign_physical_ghost_leakage H q (siteCompletion (q + 1) T.val (powersetCard_small j T))
      θ hθ hθ1 s hs hsd t ht S kernel x₀ r hr k n Subtype.val Subtype.val_injective
    simpa only [blockSubsetCost, ghostSubsetBound, Fintype.card_coe,
      (Finset.mem_powersetCard.mp T.property).2] using hh
  calc
    _ ≤ ∑ _ : (Finset.univ : Finset (Fin n)).powersetCard (j.val + 1),
        ghostSubsetBound d q θ s t r (j.val + 1) := Finset.sum_le_sum (fun T _ => hb T)
    _ = (n.choose (j.val + 1) : ℝ) * ghostSubsetBound d q θ s t r (j.val + 1) := by simp
    _ ≤ (n : ℝ) ^ (j.val + 1) * ghostSubsetBound d q θ s t r (j.val + 1) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow n (j.val + 1))
        (ghostSubsetBound_nonneg q θ s t r hθ hθ1 hr.le ht.le _)

end CausalLowerbound.PartB.ShellGeometry

import CausalLowerbound.PartB.SubsetGhostCost
import CausalLowerbound.PartB.HighComponentProbability
import CausalLowerbound.PartB.CarrierCounting

/-! The global leakage majorant is measurable, integrable, and has a
uniform bound of order n h^d t^s whenever n r^d ≤ 1. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

theorem carrierSites_subset_reachable (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    {n : ℕ} (x : Fin n → d → ℝ) (k : S) (root : Fin n) (hr : root ∈ carrierSites x₀ r k.val x) :
    carrierSites x₀ r k.val x ⊆ reachableVertices (observationGraph S x₀ r x) root := by
  intro i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ i, ?_⟩
  apply SimpleGraph.ConnectedComponent.exact
  exact common_label_same_component (fun j (b : S) => x j ∈ carrierBox x₀ r b.val)
    root i k (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hi).2

theorem carrierSites_small_off_largeCluster (n Q : ℕ) (hQ : 1 ≤ Q)
    (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hrh : r ≤ h)
    (x : Fin n → d → ℝ) (hx : x ∉ largeClusterEvent n Q x₀ r h)
    (k : activeBlocks (d := d) r h) : (carrierSites x₀ r k.val x).card ≤ Q := by
  by_cases hne : (carrierSites x₀ r k.val x).Nonempty
  · obtain ⟨root, hroot⟩ := hne
    exact (Finset.card_le_card (carrierSites_subset_reachable _ x₀ r x k root hroot)).trans
      (component_size_le_off_largeCluster n Q hQ x₀ r h hr hrh x hx root)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

def globalGhostCost (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ) (x₀ : d → ℝ)
    (r h : ℝ) {n : ℕ} (x : Fin n → d → ℝ) : ℝ :=
  ∑ k : activeBlocks (d := d) r h, smallBlockCost H Q θ t x₀ r k.val x

theorem globalGhostCost_nonneg (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r)
    {n : ℕ} (x : Fin n → d → ℝ) : 0 ≤ globalGhostCost H Q θ t x₀ r h x :=
  Finset.sum_nonneg (fun k _ => smallBlockCost_nonneg H Q θ t hθ hθ1 x₀ r hr k.val x)

theorem globalGhostCost_measurable (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (n : ℕ) :
    Measurable (fun x : Fin n → d → ℝ => globalGhostCost H Q θ t x₀ r h x) :=
  Finset.measurable_sum _ (fun k _ => smallBlockCost_measurable H Q θ t hθ hθ1 x₀ r hr k.val n)

theorem globalGhostCost_integrable (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (kernel : ℕ → FiniteLaw Ω)
    (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x : Fin n → d → ℝ => globalGhostCost H Q θ t x₀ r h x)
      (mixedDesignExperiment Q (activeBlocks r h) θ hθ hθ1 H kernel x₀ r n) :=
  integrable_finset_sum _ (fun k _ =>
    smallBlockCost_integrable H Q θ t hθ hθ1 (activeBlocks r h) kernel x₀ r hr k.val n)

theorem actual_total_leakage_le_globalGhostCost (H : DiscreteLaw ℕ) (Q : ℕ) (θ t : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r)
    {n : ℕ} (x : Fin n → d → ℝ)
    (hq : ∀ k : activeBlocks (d := d) r h, (carrierSites x₀ r k.val x).card ≤ Q) :
    (∑ k : activeBlocks (d := d) r h, if (carrierSites x₀ r k.val x).Nonempty then
      1 - evaluatedBlockWeight H Q θ t (carrierSites x₀ r k.val x)
        (siteCompletion Q _ (hq k)) (physicalBlockCoordinates x₀ r x k.val) else 0) ≤
      globalGhostCost H Q θ t x₀ r h x := by
  exact Finset.sum_le_sum (fun k _ =>
    actual_block_leakage_le_smallBlockCost H Q θ t hθ hθ1 x₀ r hr k.val x (hq k))

def ghostSubsetCoefficient (d : Type*) [Fintype d] (q : ℕ) (θ s : ℝ) (m : ℕ) : ℝ :=
  (designDensityCeiling d θ : ℝ) ^ m * (4 : ℝ) ^ (m * Fintype.card d) *
    (((1 + θ) ^ (q + 1) * ((q + 1 : ℝ) * ((2 : ℝ) ^ s * collisionMomentBound d s ^ q))) /
      (1 - θ) ^ m)

def globalGhostConstant (d : Type*) [Fintype d] (q : ℕ) (θ s : ℝ) : ℝ :=
  (7 : ℝ) ^ Fintype.card d * ∑ j : Fin (q + 1), ghostSubsetCoefficient d q θ s (j.val + 1)

theorem ghostSubsetCoefficient_nonneg (q : ℕ) (θ s : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (m : ℕ) :
    0 ≤ ghostSubsetCoefficient d q θ s m := by
  have hM := collisionMomentBound_nonneg (d := d) s
  have hc : 0 ≤ 1 - θ := by linarith
  unfold ghostSubsetCoefficient
  positivity

theorem ghostSubsetBound_factor (q : ℕ) (θ s t r : ℝ) (ht : 0 ≤ t) (m : ℕ) :
    ghostSubsetBound d q θ s t r m = ghostSubsetCoefficient d q θ s m * r ^ (m * Fintype.card d) * t ^ s := by
  unfold ghostSubsetBound ghostSubsetCoefficient
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht]
  simp only [mul_pow]
  ring

theorem smallBlockCost_integral_sparse [Nonempty d] (H : DiscreteLaw ℕ) (q : ℕ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (t : ℝ) (ht : 0 < t)
    (S : Finset (d → ℤ)) (kernel : ℕ → FiniteLaw Ω) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r)
    (k : d → ℤ) (n : ℕ) (hnr : (n : ℝ) * r ^ Fintype.card d ≤ 1) :
    (∫ x : Fin n → d → ℝ, smallBlockCost H (q + 1) θ t x₀ r k x
      ∂mixedDesignExperiment (q + 1) S θ hθ hθ1 H kernel x₀ r n) ≤
      (∑ j : Fin (q + 1), ghostSubsetCoefficient d q θ s (j.val + 1)) *
        ((n : ℝ) * r ^ Fintype.card d * t ^ s) := by
  apply (smallBlockCost_integral_le H q θ hθ hθ1 s hs hsd t ht S kernel x₀ r hr k n).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  have hp : ((n : ℝ) * r ^ Fintype.card d) ^ (j.val + 1) ≤ (n : ℝ) * r ^ Fintype.card d := by
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (by positivity) hnr) (by positivity)).trans_eq (one_mul _)
  have he : (n : ℝ) ^ (j.val + 1) * ghostSubsetBound d q θ s t r (j.val + 1) =
      ghostSubsetCoefficient d q θ s (j.val + 1) * t ^ s *
        ((n : ℝ) * r ^ Fintype.card d) ^ (j.val + 1) := by
    rw [ghostSubsetBound_factor q θ s t r ht.le, mul_pow, ← pow_mul,
      Nat.mul_comm (Fintype.card d) (j.val + 1)]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg
    (ghostSubsetCoefficient_nonneg (d := d) q θ s hθ hθ1 (j.val + 1)) (Real.rpow_nonneg ht.le s))
  convert hh using 1 <;> ring

theorem globalGhostCost_integral_le [Nonempty d] (H : DiscreteLaw ℕ) (q : ℕ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (t : ℝ) (ht : 0 < t)
    (kernel : ℕ → FiniteLaw Ω) (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hrh : r ≤ h)
    (n : ℕ) (hnr : (n : ℝ) * r ^ Fintype.card d ≤ 1) :
    (∫ x : Fin n → d → ℝ, globalGhostCost H (q + 1) θ t x₀ r h x
      ∂mixedDesignExperiment (q + 1) (activeBlocks r h) θ hθ hθ1 H kernel x₀ r n) ≤
      globalGhostConstant d q θ s * ((n : ℝ) * h ^ Fintype.card d * t ^ s) := by
  let C := ∑ j : Fin (q + 1), ghostSubsetCoefficient d q θ s (j.val + 1)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => ghostSubsetCoefficient_nonneg q θ s hθ hθ1 _)
  unfold globalGhostCost
  rw [integral_finset_sum _ (fun k _ =>
    smallBlockCost_integrable H (q + 1) θ t hθ hθ1 (activeBlocks r h) kernel x₀ r hr k.val n)]
  calc
    _ ≤ ∑ _ : activeBlocks (d := d) r h, C * ((n : ℝ) * r ^ Fintype.card d * t ^ s) :=
      Finset.sum_le_sum (fun k _ =>
        smallBlockCost_integral_sparse H q θ hθ hθ1 s hs hsd t ht (activeBlocks r h) kernel x₀ r hr k.val n hnr)
    _ = ((activeBlocks (d := d) r h).card : ℝ) * (C * ((n : ℝ) * r ^ Fintype.card d * t ^ s)) := by simp
    _ ≤ (7 * (h / r)) ^ Fintype.card d * (C * ((n : ℝ) * r ^ Fintype.card d * t ^ s)) :=
      mul_le_mul_of_nonneg_right (activeBlocks_card_bound r h hr hrh) (by positivity)
    _ = globalGhostConstant d q θ s * ((n : ℝ) * h ^ Fintype.card d * t ^ s) := by
      unfold globalGhostConstant
      dsimp only [C]
      rw [mul_pow, div_pow]
      field_simp
      ring

end CausalLowerbound.PartB.ShellGeometry

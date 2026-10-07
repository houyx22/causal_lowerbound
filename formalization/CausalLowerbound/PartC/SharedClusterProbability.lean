import CausalLowerbound.PartC.CarrierDesignMarginals
import CausalLowerbound.PartC.SharedCarrierGeometry
import CausalLowerbound.PartB.ComponentSize

/-! A measurable large-component exception for the enlarged shared-sign
graph, with its probability bounded under the actual mixed design. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt incidenceComponentFintype
variable {d K J Ω : Type*} [Fintype d] [DecidableEq d]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype Ω] {θ : ℝ}

def sharedLargeClusterEvent (n Q : ℕ) (x₀ : d → ℝ) (r h : ℝ) : Set (Fin n → d → ℝ) :=
  ⋃ e : Fin (Q + 1) ↪ Fin n, (fun x i => x (e i)) ⁻¹'
    labelledCluster Q x₀ ((5 + 10 * Q) * h) (20 * r * Q)

def sharedClusterProbabilityConstant (d : Type*) [Fintype d] (Q : ℕ) (θ : ℝ) : ℝ :=
  (designDensityCeiling d θ : ℝ) ^ (Q + 1) * (2 * (5 + 10 * Q)) ^ Fintype.card d *
    (40 * Q) ^ (Q * Fintype.card d)

theorem sharedLargeClusterEvent_measurable (n Q : ℕ) (x₀ : d → ℝ) (r h : ℝ) :
    MeasurableSet (sharedLargeClusterEvent n Q x₀ r h) := by
  apply MeasurableSet.iUnion
  intro e
  exact (labelledCluster_measurable Q x₀ _ _).preimage
    (measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i)))

theorem shared_high_component_subset_largeCluster (n Q : ℕ) (hQ : 1 ≤ Q)
    (x₀ : d → ℝ) (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hℓr : ℓ ≤ r) (hrh : r ≤ h) :
    {x | ∃ root, Q + 1 ≤ (reachableVertices
      (physicalSharedGraph (activeBlocks r h) x₀ ℓ r h x) root).card} ⊆
        sharedLargeClusterEvent n Q x₀ r h := by
  rintro x ⟨root, hroot⟩
  obtain ⟨v, hv, hc, hd⟩ := physicalSharedGraph_high_component_cluster x₀ ℓ r h
    hℓ hr hℓr hrh x root Q hQ hroot
  apply Set.mem_iUnion.mpr
  refine ⟨⟨v, hv⟩, ?_⟩
  change (x (v 0), fun i : Fin Q => x (v i.succ)) ∈
    rootedCluster Q x₀ ((5 + 10 * Q) * h) (20 * r * Q)
  exact ⟨(mem_coordinateBox _ _ _).mpr hc,
    fun i => (mem_coordinateBox _ _ _).mpr (hd i.succ)⟩

theorem shared_component_size_le_off_largeCluster (n Q : ℕ) (hQ : 1 ≤ Q)
    (x₀ : d → ℝ) (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hℓr : ℓ ≤ r) (hrh : r ≤ h)
    (x : Fin n → d → ℝ) (hx : x ∉ sharedLargeClusterEvent n Q x₀ r h) (root : Fin n) :
    (reachableVertices (physicalSharedGraph (activeBlocks r h) x₀ ℓ r h x) root).card ≤ Q := by
  by_contra hn
  apply hx
  exact shared_high_component_subset_largeCluster n Q hQ x₀ ℓ r h hℓ hr hℓr hrh ⟨root, by omega⟩

theorem shared_component_fiber_small_off_largeCluster (n Q : ℕ) (hQ : 1 ≤ Q)
    (x₀ : d → ℝ) (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hℓr : ℓ ≤ r) (hrh : r ≤ h)
    (x : Fin n → d → ℝ) (hx : x ∉ sharedLargeClusterEvent n Q x₀ r h)
    (a : Option (incidenceGraph (physicalSharedIncidence (activeBlocks r h) x₀ ℓ r h x)).ConnectedComponent) :
    Fintype.card {i // siteComponent (physicalSharedIncidence (activeBlocks r h) x₀ ℓ r h x) i = a} ≤ Q :=
  siteComponent_card_le _ Q
    (shared_component_size_le_off_largeCluster n Q hQ x₀ ℓ r h hℓ hr hℓr hrh x hx) a

theorem sharedLargeClusterEvent_probability_le
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r h : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n Q : ℕ) :
    mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n (sharedLargeClusterEvent n Q x₀ r h) ≤
      (n : ℝ≥0∞) ^ (Q + 1) *
        ((designDensityCeiling d θ : ℝ≥0∞) ^ (Q + 1) *
          (ENNReal.ofReal (2 * ((5 + 10 * Q) * h)) ^ Fintype.card d *
            ENNReal.ofReal (2 * (20 * r * Q)) ^ (Q * Fintype.card d))) := by
  let μ := mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n
  let C : ℝ≥0∞ := (designDensityCeiling d θ : ℝ≥0∞) ^ (Q + 1) *
    (ENNReal.ofReal (2 * ((5 + 10 * Q) * h)) ^ Fintype.card d *
      ENNReal.ofReal (2 * (20 * r * Q)) ^ (Q * Fintype.card d))
  have hb (e : Fin (Q + 1) ↪ Fin n) :
      μ ((fun x i => x (e i)) ⁻¹' labelledCluster Q x₀ ((5 + 10 * Q) * h) (20 * r * Q)) ≤ C := by
    have hh := mixedCarrierDesign_cylinder_le F hθ hθ1 S x₀ r H kernel n e e.injective
      (labelledCluster Q x₀ ((5 + 10 * Q) * h) (20 * r * Q))
      (labelledCluster_measurable Q x₀ ((5 + 10 * Q) * h) (20 * r * Q))
    simpa only [Fintype.card_fin, labelledCluster_volume] using hh
  have hc : Fintype.card (Fin (Q + 1) ↪ Fin n) ≤ n ^ (Q + 1) := by
    have hh := Fintype.card_le_of_injective
      (fun e : Fin (Q + 1) ↪ Fin n => (e : Fin (Q + 1) → Fin n))
      (fun e f hef => Function.Embedding.ext (congrFun hef))
    simpa using hh
  calc
    μ (sharedLargeClusterEvent n Q x₀ r h) ≤
        ∑ e : Fin (Q + 1) ↪ Fin n,
          μ ((fun x i => x (e i)) ⁻¹' labelledCluster Q x₀ ((5 + 10 * Q) * h) (20 * r * Q)) :=
      measure_iUnion_fintype_le μ _
    _ ≤ ∑ _ : Fin (Q + 1) ↪ Fin n, C := Finset.sum_le_sum (fun e _ => hb e)
    _ = Fintype.card (Fin (Q + 1) ↪ Fin n) * C := by simp
    _ ≤ (n : ℝ≥0∞) ^ (Q + 1) * C := mul_le_mul_right' (by exact_mod_cast hc) C

theorem sharedLargeClusterEvent_real_probability_le
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r h : ℝ) (hr : 0 ≤ r) (hh : 0 ≤ h)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n Q : ℕ) :
    (mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n).real (sharedLargeClusterEvent n Q x₀ r h) ≤
      sharedClusterProbabilityConstant d Q θ *
        ((n : ℝ) ^ (Q + 1) * h ^ Fintype.card d * r ^ (Q * Fintype.card d)) := by
  have hb := ENNReal.toReal_mono (by
    apply ENNReal.mul_ne_top
    · exact ENNReal.pow_ne_top (by simp)
    · apply ENNReal.mul_ne_top
      · exact ENNReal.pow_ne_top (by simp)
      · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    (sharedLargeClusterEvent_probability_le F hθ hθ1 S x₀ r h H kernel n Q)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ((5 + 10 * Q) * h)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (20 * r * Q))] at hb
  convert hb using 1
  unfold sharedClusterProbabilityConstant
  rw [show 2 * ((5 + 10 * (Q : ℝ)) * h) = (2 * (5 + 10 * Q)) * h by ring,
    show 2 * (20 * r * (Q : ℝ)) = (40 * Q) * r by ring]
  simp only [mul_pow]
  ring

end CausalLowerbound.PartC

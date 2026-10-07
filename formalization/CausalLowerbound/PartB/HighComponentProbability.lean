import CausalLowerbound.PartB.HighComponentGeometry
import CausalLowerbound.PartB.ClusterVolume
import CausalLowerbound.PartB.DesignMarginals

/-! The actual mixed-design probability of the large-component event.
The measurable exceptional set is a finite union of labelled clusters. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace CausalLowerbound.PartB.ShellGeometry
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

def largeClusterEvent (n Q : ℕ) (x₀ : d → ℝ) (r h : ℝ) : Set (Fin n → d → ℝ) :=
  ⋃ e : Fin (Q + 1) ↪ Fin n, (fun x i => x (e i)) ⁻¹'
    labelledCluster Q x₀ ((5 + 4 * Q) * h) (8 * r * Q)

def clusterProbabilityConstant (d : Type*) [Fintype d] (Q : ℕ) (θ : ℝ) : ℝ :=
  (designDensityCeiling d θ : ℝ) ^ (Q + 1) * (2 * (5 + 4 * Q)) ^ Fintype.card d *
    (16 * Q) ^ (Q * Fintype.card d)

theorem largeClusterEvent_measurable (n Q : ℕ) (x₀ : d → ℝ) (r h : ℝ) :
    MeasurableSet (largeClusterEvent n Q x₀ r h) := by
  apply MeasurableSet.iUnion
  intro e
  exact (labelledCluster_measurable Q x₀ _ _).preimage
    (measurable_pi_iff.mpr (fun i => measurable_pi_apply (e i)))

theorem high_component_subset_largeCluster (n Q : ℕ) (hQ : 1 ≤ Q)
    (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hrh : r ≤ h) :
    {x | ∃ root, Q + 1 ≤ (reachableVertices
      (observationGraph (activeBlocks r h) x₀ r x) root).card} ⊆
        largeClusterEvent n Q x₀ r h := by
  rintro x ⟨root, hroot⟩
  obtain ⟨v, hv, hc, hd⟩ := high_component_cluster x₀ r h hr hrh x root Q hQ hroot
  apply Set.mem_iUnion.mpr
  refine ⟨⟨v, hv⟩, ?_⟩
  change (x (v 0), fun i : Fin Q => x (v i.succ)) ∈
    rootedCluster Q x₀ ((5 + 4 * Q) * h) (8 * r * Q)
  exact ⟨(mem_coordinateBox _ _ _).mpr hc,
    fun i => (mem_coordinateBox _ _ _).mpr (hd i.succ)⟩

theorem component_size_le_off_largeCluster (n Q : ℕ) (hQ : 1 ≤ Q)
    (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hrh : r ≤ h)
    (x : Fin n → d → ℝ) (hx : x ∉ largeClusterEvent n Q x₀ r h) (root : Fin n) :
    (reachableVertices (observationGraph (activeBlocks r h) x₀ r x) root).card ≤ Q := by
  by_contra hn
  apply hx
  exact high_component_subset_largeCluster n Q hQ x₀ r h hr hrh ⟨root, by omega⟩

theorem largeClusterEvent_probability_le (n Q : ℕ) (S : Finset (d → ℤ))
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw Ω) (x₀ : d → ℝ) (r h : ℝ) :
    mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n (largeClusterEvent n Q x₀ r h) ≤
      (n : ℝ≥0∞) ^ (Q + 1) *
        ((designDensityCeiling d θ : ℝ≥0∞) ^ (Q + 1) *
          (ENNReal.ofReal (2 * ((5 + 4 * Q) * h)) ^ Fintype.card d *
            ENNReal.ofReal (2 * (8 * r * Q)) ^ (Q * Fintype.card d))) := by
  let μ := mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n
  let C : ℝ≥0∞ := (designDensityCeiling d θ : ℝ≥0∞) ^ (Q + 1) *
    (ENNReal.ofReal (2 * ((5 + 4 * Q) * h)) ^ Fintype.card d *
      ENNReal.ofReal (2 * (8 * r * Q)) ^ (Q * Fintype.card d))
  have hb (e : Fin (Q + 1) ↪ Fin n) :
      μ ((fun x i => x (e i)) ⁻¹' labelledCluster Q x₀ ((5 + 4 * Q) * h) (8 * r * Q)) ≤ C := by
    have hh := mixedDesign_cylinder_le Q S θ hθ hθ1 H kernel x₀ r n e e.injective
      (labelledCluster Q x₀ ((5 + 4 * Q) * h) (8 * r * Q))
      (labelledCluster_measurable Q x₀ ((5 + 4 * Q) * h) (8 * r * Q))
    simpa only [Fintype.card_fin, labelledCluster_volume] using hh
  have hc : Fintype.card (Fin (Q + 1) ↪ Fin n) ≤ n ^ (Q + 1) := by
    have hh := Fintype.card_le_of_injective
      (fun e : Fin (Q + 1) ↪ Fin n => (e : Fin (Q + 1) → Fin n))
      (fun e f hef => Function.Embedding.ext (congrFun hef))
    simpa using hh
  calc
    μ (largeClusterEvent n Q x₀ r h) ≤
        ∑ e : Fin (Q + 1) ↪ Fin n,
          μ ((fun x i => x (e i)) ⁻¹' labelledCluster Q x₀ ((5 + 4 * Q) * h) (8 * r * Q)) :=
      measure_iUnion_fintype_le μ _
    _ ≤ ∑ _ : Fin (Q + 1) ↪ Fin n, C := Finset.sum_le_sum (fun e _ => hb e)
    _ = Fintype.card (Fin (Q + 1) ↪ Fin n) * C := by simp
    _ ≤ (n : ℝ≥0∞) ^ (Q + 1) * C := mul_le_mul_right' (by exact_mod_cast hc) C

theorem high_component_probability_le (n Q : ℕ) (hQ : 1 ≤ Q)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw Ω) (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hrh : r ≤ h) :
    mixedDesignExperiment Q (activeBlocks r h) θ hθ hθ1 H kernel x₀ r n
        {x | ∃ root, Q + 1 ≤ (reachableVertices
          (observationGraph (activeBlocks r h) x₀ r x) root).card} ≤
      (n : ℝ≥0∞) ^ (Q + 1) *
        ((designDensityCeiling d θ : ℝ≥0∞) ^ (Q + 1) *
          (ENNReal.ofReal (2 * ((5 + 4 * Q) * h)) ^ Fintype.card d *
            ENNReal.ofReal (2 * (8 * r * Q)) ^ (Q * Fintype.card d))) := by
  exact (measure_mono (high_component_subset_largeCluster n Q hQ x₀ r h hr hrh)).trans
    (largeClusterEvent_probability_le n Q (activeBlocks r h) θ hθ hθ1 H kernel x₀ r h)

theorem largeClusterEvent_real_probability_le (n Q : ℕ) (S : Finset (d → ℤ))
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw Ω) (x₀ : d → ℝ) (r h : ℝ) (hr : 0 ≤ r) (hh : 0 ≤ h) :
    (mixedDesignExperiment Q S θ hθ hθ1 H kernel x₀ r n).real (largeClusterEvent n Q x₀ r h) ≤
      clusterProbabilityConstant d Q θ * ((n : ℝ) ^ (Q + 1) * h ^ Fintype.card d * r ^ (Q * Fintype.card d)) := by
  have hb := ENNReal.toReal_mono (by
    apply ENNReal.mul_ne_top
    · exact ENNReal.pow_ne_top (by simp)
    · apply ENNReal.mul_ne_top
      · exact ENNReal.pow_ne_top (by simp)
      · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    (largeClusterEvent_probability_le n Q S θ hθ hθ1 H kernel x₀ r h)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.coe_toReal, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * ((5 + 4 * Q) * h)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (8 * r * Q))] at hb
  convert hb using 1
  unfold clusterProbabilityConstant
  rw [show 2 * ((5 + 4 * (Q : ℝ)) * h) = (2 * (5 + 4 * Q)) * h by ring,
    show 2 * (8 * r * (Q : ℝ)) = (16 * Q) * r by ring]
  simp only [mul_pow]
  ring

end CausalLowerbound.PartB.ShellGeometry

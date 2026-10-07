import CausalLowerbound.PartB.PhysicalActivation
import CausalLowerbound.PartB.FinitePartialStability

/-! Actual second and fourth moments of the physical packet jitters and
the exact correction used in the smooth cubic regression. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem quarticField_bounds (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (hr : 0 < r) (x : d → ℝ) : 0 ≤ quarticField S x₀ r x ∧ quarticField S x₀ r x ≤ 1 := by
  have he : quarticField S x₀ r x =
      ∑ k ∈ S, quadraticPartition (fun i => (x i - x₀ i) / r - k i) ^ 4 := by
    simp only [quarticField, rescaled, quarticProfile, packet_local_coordinate x₀ r hr.ne']
  rw [he]
  refine ⟨Finset.sum_nonneg (fun _ _ => by positivity), ?_⟩
  have hsum := quadraticPartition_sum_sq (fun i => (x i - x₀ i) / r)
  have hs : Summable (fun k : d → ℤ => quadraticPartition (fun i => (x i - x₀ i) / r - k i) ^ 2) := by
    by_contra hn
    rw [tsum_eq_zero_of_not_summable hn] at hsum
    norm_num at hsum
  calc
    _ ≤ ∑ k ∈ S, quadraticPartition (fun i => (x i - x₀ i) / r - k i) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      have hb := (sq_le_one_iff_abs_le_one _).mpr (quadraticPartition_abs_le (fun i => (x i - x₀ i) / r - k i))
      nlinarith [sq_nonneg (quadraticPartition (fun i => (x i - x₀ i) / r - k i))]
    _ ≤ ∑' k : d → ℤ, quadraticPartition (fun i => (x i - x₀ i) / r - k i) ^ 2 :=
      Summable.sum_le_tsum S (fun _ _ => sq_nonneg _) hs
    _ = 1 := hsum

def physicalJitterWeights (x₀ : d → ℝ) (r h a t : ℝ) (x : d → ℝ)
    (k : activeBlocks (d := d) r h) : ℝ := a * t * packet (coarseBump x₀ h) x₀ r k.val x

theorem physicalJitter_variance (x₀ : d → ℝ) (r h a t : ℝ) (hr : 0 < r) (hh : 0 < h) (x : d → ℝ) :
    (∑ k, physicalJitterWeights x₀ r h a t x k ^ 2) = a ^ 2 * t ^ 2 * coarseBump x₀ h x ^ 2 := by
  simp only [physicalJitterWeights, mul_pow, ← Finset.mul_sum]
  rw [Finset.sum_coe_sort (activeBlocks r h)
    (fun k => packet (coarseBump x₀ h) x₀ r k x ^ 2), active_packet_square_sum x₀ r h hr hh]

theorem physicalJitter_fourth_sum (x₀ : d → ℝ) (r h a t : ℝ) (hr : 0 < r) (x : d → ℝ) :
    (∑ k, physicalJitterWeights x₀ r h a t x k ^ 4) =
      a ^ 4 * t ^ 4 * coarseBump x₀ h x ^ 4 * quarticField (activeBlocks r h) x₀ r x := by
  simp only [physicalJitterWeights, packet, mul_pow, ← mul_assoc, ← Finset.mul_sum]
  rw [Finset.sum_coe_sort (activeBlocks r h)
    (fun k => quadraticPartition (fun i => (x i - x₀ i) / r - k i) ^ 4)]
  congr 1
  simp only [quarticField, rescaled, quarticProfile, packet_local_coordinate x₀ r hr.ne']

theorem physicalJitter_correction (x₀ : d → ℝ) (r h a t : ℝ) (hr : 0 < r) (hh : 0 < h) (x : d → ℝ) :
    3 * packetEta (activeBlocks r h) x₀ r h a t x * (∑ k, physicalJitterWeights x₀ r h a t x k ^ 2) =
      3 * (∑ k, physicalJitterWeights x₀ r h a t x k ^ 2) ^ 2 -
        2 * ∑ k, physicalJitterWeights x₀ r h a t x k ^ 4 := by
  rw [physicalJitter_variance x₀ r h a t hr hh, physicalJitter_fourth_sum x₀ r h a t hr]
  unfold packetEta
  ring

theorem physicalJitter_variance_le_one (x₀ : d → ℝ) (r h a t : ℝ)
    (hr : 0 < r) (hh : 0 < h) (hat : a ^ 2 * t ^ 2 ≤ 1) (x : d → ℝ) :
    (∑ k, physicalJitterWeights x₀ r h a t x k ^ 2) ≤ 1 := by
  rw [physicalJitter_variance x₀ r h a t hr hh]
  have hG := coarseBump_range x₀ h x
  have hG2 : coarseBump x₀ h x ^ 2 ≤ 1 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hG2 (mul_nonneg (sq_nonneg a) (sq_nonneg t))).trans (by simpa using hat)

theorem physical_packetEta_bounds (x₀ : d → ℝ) (r h a t : ℝ)
    (hr : 0 < r) (hat : a ^ 2 * t ^ 2 ≤ 1) (x : d → ℝ) :
    0 ≤ packetEta (activeBlocks r h) x₀ r h a t x ∧ packetEta (activeBlocks r h) x₀ r h a t x ≤ 1 := by
  have hq := quarticField_bounds (activeBlocks r h) x₀ r hr x
  have hG := coarseBump_range x₀ h x
  have hv0 : 0 ≤ a ^ 2 * t ^ 2 * coarseBump x₀ h x ^ 2 := by positivity
  have hv1 : a ^ 2 * t ^ 2 * coarseBump x₀ h x ^ 2 ≤ 1 := by
    have hG2 : coarseBump x₀ h x ^ 2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hG2 (mul_nonneg (sq_nonneg a) (sq_nonneg t))).trans (by simpa using hat)
  have he : packetEta (activeBlocks r h) x₀ r h a t x =
      (a ^ 2 * t ^ 2 * coarseBump x₀ h x ^ 2) * (3 - 2 * quarticField (activeBlocks r h) x₀ r x) / 3 := by
    unfold packetEta
    ring
  rw [he]
  constructor
  · exact div_nonneg (mul_nonneg hv0 (by linarith)) (by norm_num)
  · have hb := mul_le_mul_of_nonneg_left (show 3 - 2 * quarticField (activeBlocks r h) x₀ r x ≤ 3 by linarith) hv0
    nlinarith

theorem physicalJitter_target (x₀ : d → ℝ) (r h a b t : ℝ)
    (hr : 0 < r) (hh : 0 < h) (ha : a ≠ 0) (x : d → ℝ) :
    (b / a) * (∑ k, physicalJitterWeights x₀ r h a t x k ^ 2) = targetField x₀ h (a * b * t ^ 2) x := by
  rw [physicalJitter_variance x₀ r h a t hr hh]
  unfold targetField
  field_simp
  ring

end CausalLowerbound.PartB.ShellGeometry

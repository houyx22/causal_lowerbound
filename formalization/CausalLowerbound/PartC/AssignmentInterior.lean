import CausalLowerbound.PartC.AssignmentTransition
import CausalLowerbound.PartC.AssignmentMultiplier

/-! Away from the measured transition layer, exactly one physical block
has assignment weight one and all other assignment weights vanish. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def assignmentWeight (w : ℝ) (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) (x : d → ℝ) : ℝ :=
  rescaled (assignmentPartition w) (packetCenter x₀ r k) r x

theorem assignmentWeight_bounds (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) (x : d → ℝ) :
    0 ≤ assignmentWeight w x₀ r k x ∧ assignmentWeight w x₀ r k x ≤ 1 :=
  assignmentPartition_bounds w hw hw1 _

theorem assignmentWeight_sum (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (x : d → ℝ) :
    (∑' k : d → ℤ, assignmentWeight w x₀ r k x) = 1 := by
  simp only [assignmentWeight, rescaled, packet_local_coordinate x₀ r hr.ne']
  exact assignmentPartition_sum w hw hw1 _

theorem assignmentWeight_summable (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (x : d → ℝ) :
    Summable (fun k : d → ℤ => assignmentWeight w x₀ r k x) := by
  by_contra hn
  have hz := tsum_eq_zero_of_not_summable hn
  rw [assignmentWeight_sum w hw hw1 x₀ r hr x] at hz
  norm_num at hz

theorem assignmentWeight_one_excludes (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (x : d → ℝ) (k j : d → ℤ)
    (hk : assignmentWeight w x₀ r k x = 1) (hjk : j ≠ k) :
    assignmentWeight w x₀ r j x = 0 := by
  have hs := (assignmentWeight_summable w hw hw1 x₀ r hr x).sum_le_tsum {j, k}
    (fun i _hi => (assignmentWeight_bounds w hw hw1 x₀ r i x).1)
  rw [Finset.sum_pair hjk, hk, assignmentWeight_sum w hw hw1 x₀ r hr x] at hs
  linarith [(assignmentWeight_bounds w hw hw1 x₀ r j x).1]

theorem assignmentWeight_ne_zero_mem_active (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (x : d → ℝ)
    (hx : x ∈ coordinateBox x₀ h) (k : d → ℤ) (hk : assignmentWeight w x₀ r k x ≠ 0) :
    k ∈ activeBlocks (d := d) r h := by
  rw [assignmentWeight, rescaled, packet_local_coordinate x₀ r hr.ne'] at hk
  have hu := assignmentPartition_support w hw (subset_closure hk)
  apply Fintype.mem_piFinset.mpr
  intro i
  have hlocal : |(x i - x₀ i) / r - k i| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hu.1 i, hu.2 i]
  have hy : |(x i - x₀ i) / r| ≤ h / r := by
    rw [abs_div, abs_of_pos hr]
    exact div_le_div_of_nonneg_right ((mem_coordinateBox _ _ _).mp hx i) hr.le
  have htri := abs_sub ((x i - x₀ i) / r) ((x i - x₀ i) / r - k i)
  have he : (x i - x₀ i) / r - ((x i - x₀ i) / r - k i) = (k i : ℝ) := by ring
  rw [he] at htri
  have hki : |(k i : ℝ)| ≤ h / r + 1 := by linarith
  have hkM := hki.trans (Int.le_ceil (h / r + 1))
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (abs_le.mp hkM).1
  · exact_mod_cast (abs_le.mp hkM).2

theorem assignment_exists_unique (S : Finset (d → ℤ)) (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (x : d → ℝ)
    (hcover : ∀ k, assignmentWeight w x₀ r k x ≠ 0 → k ∈ S)
    (hx : x ∉ assignmentTransitionUnion S w x₀ r) :
    ∃! k : d → ℤ, k ∈ S ∧ assignmentWeight w x₀ r k x = 1 := by
  have hex : ∃ k : d → ℤ, assignmentWeight w x₀ r k x ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hs := assignmentWeight_sum w hw hw1 x₀ r hr x
    simp only [hn, tsum_zero] at hs
    norm_num at hs
  obtain ⟨k, hk⟩ := hex
  have hkS := hcover k hk
  have hk1 : assignmentWeight w x₀ r k x = 1 := by
    by_contra hn
    apply hx
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hkS, ⟨hk, hn⟩⟩⟩
  refine ⟨k, ⟨hkS, hk1⟩, fun j hj => ?_⟩
  by_contra hjk
  have hz := assignmentWeight_one_excludes w hw hw1 x₀ r hr x k j hk1 hjk
  linarith [hj.2]

theorem active_assignment_exists_unique (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (x : d → ℝ)
    (hx : x ∈ coordinateBox x₀ h)
    (htr : x ∉ assignmentTransitionUnion (activeBlocks r h) w x₀ r) :
    ∃! k : d → ℤ, k ∈ activeBlocks r h ∧ assignmentWeight w x₀ r k x = 1 :=
  assignment_exists_unique _ w hw hw1 x₀ r hr x
    (assignmentWeight_ne_zero_mem_active w hw hw1 x₀ r h hr x hx) htr

theorem assignmentMultiplier_zero_of_weight_zero (c w : ℝ) (x₀ : d → ℝ) (r : ℝ)
    (k : d → ℤ) (x : d → ℝ) (hx : assignmentWeight w x₀ r k x = 0) :
    rescaled (assignmentMultiplier c w) (packetCenter x₀ r k) r x = 0 := by
  change assignmentPartition w _ / positiveFloor c (linearPartition _) = 0
  rw [show assignmentPartition w (r⁻¹ • (x - packetCenter x₀ r k)) = 0 from hx, zero_div]

end CausalLowerbound.PartC

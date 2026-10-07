import CausalLowerbound.PartC.AssignmentInterior
import CausalLowerbound.PartB.CarrierCounting

/-! The blocks incident to a finite configuration cover every effective
assignment. Their number is bounded by the number of observations times
the fixed carrier-overlap constant. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I]

theorem coarseBump_nonzero_mem_coordinateBox (x₀ : d → ℝ) (h : ℝ) (hh : 0 < h)
    (x : d → ℝ) (hx : coarseBump x₀ h x ≠ 0) : x ∈ coordinateBox x₀ h := by
  have hs := quadraticPartition_support (subset_tsupport _ hx)
  apply (mem_coordinateBox x₀ h x).mpr
  intro a
  have ha : |h⁻¹ * (x a - x₀ a)| ≤ 1 := abs_le.mpr ⟨hs.1 a, hs.2 a⟩
  have hb : |(x a - x₀ a) / h| ≤ 1 := by
    simpa only [div_eq_mul_inv, mul_comm] using ha
  rw [abs_div, abs_of_pos hh] at hb
  exact (div_le_one hh).mp hb

theorem assignmentWeight_nonzero_mem_carrierBox (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (x₀ : d → ℝ) (r : ℝ) (hr : r ≠ 0) (k : d → ℤ) (x : d → ℝ)
    (hk : assignmentWeight w x₀ r k x ≠ 0) : x ∈ carrierBox x₀ r k := by
  have he : assignmentWeight w x₀ r k x = assignmentPartition w (localCoordinate x₀ r k x) := by
    simp only [assignmentWeight, rescaled, packet_local_coordinate x₀ r hr, localCoordinate]
    rfl
  rw [he] at hk
  have hs := assignmentPartition_support w hw (subset_closure hk)
  constructor <;> intro a
  · change (-2 : ℝ) ≤ localCoordinate x₀ r k x a
    linarith [hs.1 a]
  · change localCoordinate x₀ r k x a ≤ (2 : ℝ)
    linarith [hs.2 a]

theorem mem_configurationBlocks (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (x : I → d → ℝ) (k : d → ℤ) :
    k ∈ configurationBlocks S x₀ r x ↔ k ∈ S ∧ ∃ i, x i ∈ carrierBox x₀ r k := by
  constructor
  · intro hk
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hk
    exact ⟨(Finset.mem_filter.mp hi).1, i, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨hk, i, hi⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨hk, hi⟩⟩

theorem configurationBlocks_subset (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (x : I → d → ℝ) : configurationBlocks S x₀ r x ⊆ S :=
  fun k hk => ((mem_configurationBlocks S x₀ r x k).mp hk).1

theorem configurationBlocks_supported_cover (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hh : 0 < h) (x : I → d → ℝ)
    (i : I) (hi : coarseBump x₀ h (x i) ≠ 0) (k : d → ℤ)
    (hk : assignmentWeight w x₀ r k (x i) ≠ 0) :
    k ∈ configurationBlocks (activeBlocks r h) x₀ r x := by
  apply (mem_configurationBlocks _ x₀ r x k).mpr
  exact ⟨assignmentWeight_ne_zero_mem_active w hw hw1 x₀ r h hr (x i)
    (coarseBump_nonzero_mem_coordinateBox x₀ h hh (x i) hi) k hk,
    i, assignmentWeight_nonzero_mem_carrierBox w hw hw1 x₀ r hr.ne' k (x i) hk⟩

theorem assignmentTransitionUnion_mono (S T : Finset (d → ℤ)) (hST : S ⊆ T)
    (w : ℝ) (x₀ : d → ℝ) (r : ℝ) :
    assignmentTransitionUnion S w x₀ r ⊆ assignmentTransitionUnion T w x₀ r := by
  intro x hx
  obtain ⟨k, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hk, hx⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hST hk, hx⟩⟩

theorem configurationBlocks_off_transition (S : Finset (d → ℤ)) (w : ℝ) (x₀ : d → ℝ) (r : ℝ)
    (x : I → d → ℝ) (i : I) (hi : x i ∉ assignmentTransitionUnion S w x₀ r) :
    x i ∉ assignmentTransitionUnion (configurationBlocks S x₀ r x) w x₀ r :=
  fun hx => hi (assignmentTransitionUnion_mono _ S (configurationBlocks_subset S x₀ r x) w x₀ r hx)

end CausalLowerbound.PartC

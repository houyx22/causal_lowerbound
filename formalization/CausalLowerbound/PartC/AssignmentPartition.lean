import CausalLowerbound.PartC.AssignmentWindow
import CausalLowerbound.PartC.LinearPartition

/-! Tensor assignment partitions. Exact partition of unity, a central
plateau, and support inside the region where the carried partition has
a fixed positive lower bound. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff
namespace CausalLowerbound.PartC
open Wiener
variable {d : Type*} [Fintype d]

def assignmentPartition (w : ℝ) (x : d → ℝ) : ℝ := ∏ i, assignmentWindow w (x i)
def assignmentPartitionComplex (w : ℝ) (x : d → ℝ) : ℂ := (assignmentPartition w x : ℂ)

theorem assignmentPartitionComplex_prod (w : ℝ) (x : d → ℝ) :
    assignmentPartitionComplex w x = ∏ i, (assignmentWindow w (x i) : ℂ) := by
  simp only [assignmentPartitionComplex, assignmentPartition, Complex.ofReal_prod]

theorem assignmentPartition_smooth (w : ℝ) : ContDiff ℝ ∞ (assignmentPartition (d := d) w) := by
  apply contDiff_prod
  intro i _
  exact (assignmentWindow_smooth w).comp (contDiff_apply ℝ ℝ i)

theorem assignmentPartition_bounds (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) (x : d → ℝ) :
    0 ≤ assignmentPartition w x ∧ assignmentPartition w x ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i _ => (assignmentWindow_bounds w (x i) hw hw1).1)
  · exact Finset.prod_le_one (fun i _ => (assignmentWindow_bounds w (x i) hw hw1).1)
      (fun i _ => (assignmentWindow_bounds w (x i) hw hw1).2)

theorem assignmentPartition_support (w : ℝ) (hw : 0 < w) :
    tsupport (assignmentPartition (d := d) w) ⊆
      Set.Icc (fun _ => -(1 + w) / 2) (fun _ => (1 + w) / 2) := by
  classical
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hi (i : d) : assignmentWindow w (x i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
  exact ⟨fun i => (assignmentWindow_support w (x i) hw (hi i)).1.le,
    fun i => (assignmentWindow_support w (x i) hw (hi i)).2.le⟩

theorem assignmentPartition_compact (w : ℝ) (hw : 0 < w) :
    HasCompactSupport (assignmentPartition (d := d) w) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (assignmentPartition_support w hw)

theorem assignmentPartition_plateau (w : ℝ) (hw : 0 < w) (x : d → ℝ)
    (hx : x ∈ Set.Icc (fun _ => -(1 - w) / 2) (fun _ => (1 - w) / 2)) :
    assignmentPartition w x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  exact assignmentWindow_plateau w (x i) hw ⟨hx.1 i, hx.2 i⟩

theorem assignmentPartition_periodize_cube (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (x : d → ℝ) (hx : x ∈ Set.Icc 0 1) :
    periodize (assignmentPartitionComplex w) (fun _ => 1) x = 1 := by
  classical
  let box : d → Finset ℤ := fun _ => {0, -1}
  have hz (k : d → ℤ) (hk : k ∉ Fintype.piFinset box) :
      assignmentPartitionComplex w (latticeTranslate (fun _ => 1) k x) = 0 := by
    have hex : ∃ i, k i ∉ box i := by simpa only [Fintype.mem_piFinset, not_forall] using hk
    obtain ⟨i, hi⟩ := hex
    rw [assignmentPartitionComplex_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa only [latticeTranslate, Nat.cast_one, one_mul, Complex.ofReal_eq_zero] using
      assignmentWindow_integer_zero w (x i) hw hw1 ⟨hx.1 i, hx.2 i⟩ (k i) hi
  rw [periodize, tsum_eq_sum hz]
  simp only [assignmentPartitionComplex_prod, latticeTranslate, Nat.cast_one, one_mul]
  rw [← Finset.prod_univ_sum box (fun i k => (assignmentWindow w (x i + k) : ℂ))]
  apply Finset.prod_eq_one
  intro i _
  simp only [box, Finset.sum_insert (by norm_num : (0 : ℤ) ∉ {-1}), Finset.sum_singleton,
    Int.cast_zero, add_zero, Int.cast_neg, Int.cast_one, ← Complex.ofReal_add]
  norm_num only [Int.cast_negSucc, Nat.cast_zero, zero_add]
  simpa only [sub_eq_add_neg, Complex.ofReal_add, Complex.ofReal_one] using
    congrArg Complex.ofReal (assignmentWindow_pair w (x i) hw hw1 ⟨hx.1 i, hx.2 i⟩)

theorem assignmentPartition_periodize (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) (x : d → ℝ) :
    periodize (assignmentPartitionComplex w) (fun _ => 1) x = 1 := by
  let k : d → ℤ := fun i => -⌊x i⌋
  have hx : latticeTranslate (fun _ => 1) k x ∈ Set.Icc 0 1 := by
    constructor
    · intro i
      simp only [latticeTranslate, k, Nat.cast_one, one_mul, Int.cast_neg, Pi.zero_apply]
      linarith [Int.floor_le (x i)]
    · intro i
      simp only [latticeTranslate, k, Nat.cast_one, one_mul, Int.cast_neg, Pi.one_apply]
      linarith [Int.lt_floor_add_one (x i)]
  rw [← periodize_lattice_invariant (assignmentPartitionComplex w) (fun _ => 1) k x]
  exact assignmentPartition_periodize_cube w hw hw1 _ hx

theorem assignmentPartition_sum (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) (x : d → ℝ) :
    (∑' k : d → ℤ, assignmentPartition w (fun i => x i - k i)) = 1 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, Complex.ofReal_one]
  have he := (Equiv.neg (d → ℤ)).tsum_eq
    (fun k => assignmentPartitionComplex w (latticeTranslate (fun _ => 1) k x))
  have he' : (∑' k : d → ℤ, (assignmentPartition w (fun i => x i - k i) : ℂ)) =
      periodize (assignmentPartitionComplex w) (fun _ => 1) x := by
    have ht (k : d → ℤ) : latticeTranslate (fun _ => 1) (-k) x = (fun i => x i - k i) := by
      funext i
      simp [latticeTranslate, sub_eq_add_neg]
    simpa only [periodize, assignmentPartitionComplex, Equiv.neg_apply, ht] using he
  rw [he', assignmentPartition_periodize w hw hw1]

theorem assignmentPartition_carried_lower_bound :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (w : ℝ), 0 < w → w ≤ 1 / 2 →
      ∀ x ∈ tsupport (assignmentPartition (d := d) w), c ≤ linearPartition x := by
  obtain ⟨c, hc, hc1, hbound⟩ := linearPartition_central_lower_bound (d := d)
  refine ⟨c, hc, hc1, fun w hw hw1 x hx => hbound x ?_⟩
  have hh := assignmentPartition_support w hw hx
  constructor <;> intro i <;> linarith [hh.1 i, hh.2 i]

end CausalLowerbound.PartC

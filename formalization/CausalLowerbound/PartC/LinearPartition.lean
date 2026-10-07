import CausalLowerbound.PartB.QuadraticPartition

/-! The smooth linear partition for Part C is the square of the already
constructed quadratic partition. Its central lower bound follows from
strict positivity and compactness. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff
namespace CausalLowerbound.PartC
variable {d : Type*} [Fintype d]

theorem quadraticWindow_pos {x : ℝ} (hx : -1 < x ∧ x < 1) :
    0 < PartB.quadraticWindow x := by
  have hπ : 0 < Real.pi / 2 := by positivity
  have hc : Real.pi / 2 * Real.smoothTransition x < Real.pi / 2 :=
    (mul_lt_mul_of_pos_left (Real.smoothTransition.lt_one_of_lt_one hx.2) hπ).trans_eq (mul_one _)
  have hc0 : 0 ≤ Real.pi / 2 * Real.smoothTransition x :=
    mul_nonneg hπ.le (Real.smoothTransition.nonneg x)
  have hs : 0 < Real.pi / 2 * Real.smoothTransition (x + 1) :=
    mul_pos hπ (Real.smoothTransition.pos_of_pos (by linarith [hx.1]))
  have hs1 : Real.pi / 2 * Real.smoothTransition (x + 1) ≤ Real.pi / 2 :=
    mul_le_of_le_one_right hπ.le (Real.smoothTransition.le_one _)
  exact mul_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith, hc⟩)
    (Real.sin_pos_of_pos_of_lt_pi hs (by linarith [Real.pi_pos]))

def linearPartition (x : d → ℝ) : ℝ := PartB.quadraticPartition x ^ 2

theorem linearPartition_smooth : ContDiff ℝ ∞ (linearPartition (d := d)) :=
  PartB.quadraticPartition_smooth.pow 2

theorem linearPartition_support :
    tsupport (linearPartition (d := d)) ⊆ Set.Icc (fun _ => -1) (fun _ => 1) := by
  have hh : tsupport (linearPartition (d := d)) ⊆ tsupport PartB.quadraticPartition := by
    change tsupport (fun x : d → ℝ => PartB.quadraticPartition x ^ 2) ⊆ _
    simpa only [pow_two] using
      (tsupport_mul_subset_left :
        tsupport (fun x : d → ℝ => PartB.quadraticPartition x * PartB.quadraticPartition x) ⊆
          tsupport PartB.quadraticPartition)
  exact hh.trans PartB.quadraticPartition_support

theorem linearPartition_compact : HasCompactSupport (linearPartition (d := d)) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure linearPartition_support

theorem linearPartition_bounds (x : d → ℝ) : 0 ≤ linearPartition x ∧ linearPartition x ≤ 1 := by
  have h0 := PartB.quadraticPartition_nonneg x
  have h1 := (abs_le.mp (PartB.quadraticPartition_abs_le x)).2
  unfold linearPartition
  exact ⟨sq_nonneg _, by nlinarith⟩

theorem linearPartition_pos (x : d → ℝ) (hx : ∀ i, -1 < x i ∧ x i < 1) :
    0 < linearPartition x := by
  have hp : 0 < PartB.quadraticPartition x :=
    Finset.prod_pos (fun i _ => quadraticWindow_pos (hx i))
  exact sq_pos_of_pos hp

@[simp] theorem linearPartition_zero : linearPartition (0 : d → ℝ) = 1 := by
  simp [linearPartition]

theorem linearPartition_sum (x : d → ℝ) :
    (∑' k : d → ℤ, linearPartition (fun i => x i - k i)) = 1 :=
  PartB.quadraticPartition_sum_sq x

theorem linearPartition_central_lower_bound :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ x ∈ Set.Icc (fun _ : d => (-3 / 4 : ℝ)) (fun _ => (3 / 4 : ℝ)), c ≤ linearPartition x := by
  have hne : (Set.Icc (fun _ : d => (-3 / 4 : ℝ)) (fun _ => (3 / 4 : ℝ))).Nonempty := by
    refine ⟨0, ?_, ?_⟩ <;> intro i <;> norm_num
  obtain ⟨x, hx, hm⟩ := isCompact_Icc.exists_isMinOn hne linearPartition_smooth.continuous.continuousOn
  refine ⟨linearPartition x, linearPartition_pos x ?_, (linearPartition_bounds x).2, ?_⟩
  · intro i
    constructor <;> linarith [hx.1 i, hx.2 i]
  · intro y hy
    exact hm hy

end CausalLowerbound.PartC

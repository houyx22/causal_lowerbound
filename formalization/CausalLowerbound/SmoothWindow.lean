import CausalLowerbound.WienerPeriodization
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! An explicit smooth compact window whose integer translates sum to one.
It converts periodic coordinates into a compact Euclidean representation. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators

namespace CausalLowerbound.Wiener

def smoothWindow (x : ℝ) : ℝ := Real.smoothTransition (x + 1) - Real.smoothTransition x

theorem smoothWindow_left {x : ℝ} (hx : x ≤ -1) : smoothWindow x = 0 := by
  rw [smoothWindow, Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_self]

theorem smoothWindow_right {x : ℝ} (hx : 1 ≤ x) : smoothWindow x = 0 := by
  rw [smoothWindow, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le hx, sub_self]

theorem smoothWindow_support {x : ℝ} (hx : smoothWindow x ≠ 0) : -1 < x ∧ x < 1 := by
  exact ⟨lt_of_not_ge (fun h => hx (smoothWindow_left h)),
    lt_of_not_ge (fun h => hx (smoothWindow_right h))⟩

theorem smoothWindow_smooth : ContDiff ℝ ∞ smoothWindow :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem smoothWindow_pair (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    smoothWindow x + smoothWindow (x - 1) = 1 := by
  have ha := Real.smoothTransition.one_of_one_le (show 1 ≤ x + 1 by linarith [hx.1])
  have hb := Real.smoothTransition.zero_of_nonpos (show x - 1 ≤ 0 by linarith [hx.2])
  simp only [smoothWindow, sub_add_cancel, ha, hb]
  ring

theorem smoothWindow_integer_zero (x : ℝ) (hx : x ∈ Set.Icc 0 1) (k : ℤ)
    (hk : k ∉ ({0, -1} : Finset ℤ)) : smoothWindow (x + k) = 0 := by
  have hk' : k ≠ 0 ∧ k ≠ -1 := by simpa using hk
  by_cases h : 0 ≤ k
  · have hi : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    exact smoothWindow_right (by linarith [hx.1])
  · have hi : (k : ℝ) ≤ -2 := by exact_mod_cast (show k ≤ -2 by omega)
    exact smoothWindow_left (by linarith [hx.2])

variable {α : Type*} [Fintype α]

def windowProduct (x : α → ℝ) : ℂ := ∏ i, (smoothWindow (x i) : ℂ)

theorem windowProduct_smooth : ContDiff ℝ ∞ (windowProduct (α := α)) := by
  apply contDiff_prod
  intro i _
  exact Complex.ofRealCLM.contDiff.comp (smoothWindow_smooth.comp (contDiff_apply ℝ ℝ i))

theorem windowProduct_support :
    tsupport (windowProduct (α := α)) ⊆ Set.Icc (fun _ => -1) (fun _ => 1) := by
  classical
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h (i : α) : smoothWindow (x i) ≠ 0 := by
    have hi := (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
    exact fun hzero => hi (by simp [hzero])
  exact ⟨fun i => (smoothWindow_support (h i)).1.le,
    fun i => (smoothWindow_support (h i)).2.le⟩

theorem windowProduct_compact : HasCompactSupport (windowProduct (α := α)) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure windowProduct_support

theorem periodize_windowProduct_cube (x : α → ℝ) (hx : x ∈ Set.Icc 0 1) :
    periodize windowProduct (fun _ => 1) x = 1 := by
  classical
  let box : α → Finset ℤ := fun _ => {0, -1}
  have hz (k : α → ℤ) (hk : k ∉ Fintype.piFinset box) :
      windowProduct (latticeTranslate (fun _ => 1) k x) = 0 := by
    have hex : ∃ i, k i ∉ box i := by simpa only [Fintype.mem_piFinset, not_forall] using hk
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simpa only [latticeTranslate, Nat.cast_one, one_mul, Complex.ofReal_eq_zero] using
      smoothWindow_integer_zero (x i) ⟨hx.1 i, hx.2 i⟩ (k i) hi
  rw [periodize, tsum_eq_sum hz]
  simp only [windowProduct, latticeTranslate, Nat.cast_one, one_mul]
  rw [← Finset.prod_univ_sum box (fun i k => (smoothWindow (x i + k) : ℂ))]
  apply Finset.prod_eq_one
  intro i _
  simp only [box, Finset.sum_insert (by norm_num : (0 : ℤ) ∉ {-1}), Finset.sum_singleton,
    Int.cast_zero, add_zero, Int.cast_neg, Int.cast_one, ← Complex.ofReal_add]
  norm_num only [Int.cast_negSucc, Nat.cast_zero, zero_add]
  simpa only [sub_eq_add_neg, Complex.ofReal_add, Complex.ofReal_one] using
    congrArg Complex.ofReal (smoothWindow_pair (x i) ⟨hx.1 i, hx.2 i⟩)

theorem periodize_windowProduct (x : α → ℝ) :
    periodize windowProduct (fun _ => 1) x = 1 := by
  let k : α → ℤ := fun i => -⌊x i⌋
  have hx : latticeTranslate (fun _ => 1) k x ∈ Set.Icc 0 1 := by
    constructor
    · intro i
      simp only [latticeTranslate, k, Nat.cast_one, one_mul, Int.cast_neg, Pi.zero_apply]
      linarith [Int.floor_le (x i)]
    · intro i
      simp only [latticeTranslate, k, Nat.cast_one, one_mul, Int.cast_neg, Pi.one_apply]
      linarith [Int.lt_floor_add_one (x i)]
  rw [← periodize_lattice_invariant windowProduct (fun _ => 1) k x]
  exact periodize_windowProduct_cube _ hx

/-- Multiplying by the fixed window preserves a periodic function after
periodization; the compact representation is exact. -/
theorem periodize_window_mul (f : (α → ℝ) → ℂ)
    (hf : ∀ k x, f (latticeTranslate (fun _ => 1) k x) = f x) (x : α → ℝ) :
    periodize (fun y => windowProduct y * f y) (fun _ => 1) x = f x := by
  simp only [periodize, hf, tsum_mul_right]
  change periodize windowProduct (fun _ => 1) x * f x = f x
  rw [periodize_windowProduct, one_mul]

end CausalLowerbound.Wiener

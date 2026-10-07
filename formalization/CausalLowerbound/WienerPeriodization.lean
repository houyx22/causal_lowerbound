import CausalLowerbound.WienerFourier
import CausalLowerbound.SmoothCompact
import Mathlib.Data.Int.Interval

/-! Actual periodization of compact Euclidean profiles with independently
chosen positive integer periods. Local finiteness, smoothness and the absence
of extra copies on the central support are proved from compact support. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff Topology
open Filter

namespace CausalLowerbound.Wiener

variable {α : Type*} [Fintype α]

def latticeTranslate (N : α → ℕ) (k : α → ℤ) (x : α → ℝ) : α → ℝ :=
  fun i => x i + (N i : ℝ) * (k i : ℝ)

def periodize (f : (α → ℝ) → ℂ) (N : α → ℕ) (x : α → ℝ) : ℂ :=
  ∑' k : α → ℤ, f (latticeTranslate N k x)

theorem periodize_lattice_invariant (f : (α → ℝ) → ℂ) (N : α → ℕ)
    (q : α → ℤ) (x : α → ℝ) :
    periodize f N (latticeTranslate N q x) = periodize f N x := by
  have he : ∀ k : α → ℤ, latticeTranslate N k (latticeTranslate N q x) =
      latticeTranslate N (k + q) x := by
    intro k; funext i
    simp only [latticeTranslate, Pi.add_apply, Int.cast_add]
    ring
  simp only [periodize, he]
  exact (Equiv.addRight q).tsum_eq (fun k => f (latticeTranslate N k x))

theorem periodize_finite_on_compact (f : (α → ℝ) → ℂ) (hf : HasCompactSupport f)
    (N : α → ℕ) (hN : ∀ i, N i ≠ 0) (K : Set (α → ℝ)) (hK : IsCompact K) :
    ∃ S : Finset (α → ℤ), ∀ x ∈ K, ∀ k ∉ S, f (latticeTranslate N k x) = 0 := by
  classical
  obtain ⟨R, hR⟩ := hf.isBounded.exists_norm_le
  obtain ⟨A, hA⟩ := hK.isBounded.exists_norm_le
  let M : ℤ := ⌈R + A⌉
  let S := Fintype.piFinset (fun _ : α => Finset.Icc (-M) M)
  refine ⟨S, ?_⟩
  intro x hx k hk
  by_contra hn
  have hy : ‖latticeTranslate N k x‖ ≤ R := hR _ (subset_tsupport f hn)
  have hx' := hA x hx
  apply hk
  apply Fintype.mem_piFinset.mpr
  intro i
  have hn1 : (1 : ℝ) ≤ N i := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hN i)
  have hi : |(k i : ℝ)| ≤ R + A := by
    calc
      _ ≤ (N i : ℝ) * |(k i : ℝ)| := le_mul_of_one_le_left (abs_nonneg _) hn1
      _ = |(latticeTranslate N k x) i - x i| := by
        simp [latticeTranslate, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ N i from Nat.cast_nonneg _)]
      _ ≤ |(latticeTranslate N k x) i| + |x i| := abs_sub _ _
      _ ≤ R + A := add_le_add ((norm_le_pi_norm _ i).trans hy) ((norm_le_pi_norm x i).trans hx')
  have hM : |(k i : ℝ)| ≤ (M : ℝ) := hi.trans (Int.le_ceil _)
  rw [Finset.mem_Icc]
  constructor
  · exact_mod_cast (abs_le.mp hM).1
  · exact_mod_cast (abs_le.mp hM).2

theorem periodize_eq_finite_sum (f : (α → ℝ) → ℂ) (N : α → ℕ) (x : α → ℝ)
    (S : Finset (α → ℤ)) (hS : ∀ k ∉ S, f (latticeTranslate N k x) = 0) :
    periodize f N x = ∑ k ∈ S, f (latticeTranslate N k x) :=
  tsum_eq_sum hS

theorem periodize_continuous (f : (α → ℝ) → ℂ) (hf : HasCompactSupport f)
    (hc : Continuous f) (N : α → ℕ) (hN : ∀ i, N i ≠ 0) : Continuous (periodize f N) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨S, hS⟩ := periodize_finite_on_compact f hf N hN (Metric.closedBall x 1) (isCompact_closedBall _ _)
  have hcont : Continuous (fun y => ∑ k ∈ S, f (latticeTranslate N k y)) := by
    apply continuous_finset_sum
    intro k _
    exact hc.comp (continuous_id.add continuous_const)
  apply hcont.continuousAt.congr_of_eventuallyEq
  filter_upwards [Metric.closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
  exact periodize_eq_finite_sum f N y S (hS y hy)

theorem periodize_contDiff (f : (α → ℝ) → ℂ) (hf : HasCompactSupport f)
    (hc : ContDiff ℝ ∞ f) (N : α → ℕ) (hN : ∀ i, N i ≠ 0) : ContDiff ℝ ∞ (periodize f N) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨S, hS⟩ := periodize_finite_on_compact f hf N hN (Metric.closedBall x 1) (isCompact_closedBall _ _)
  have hcont : ContDiff ℝ ∞ (fun y => ∑ k ∈ S, f (latticeTranslate N k y)) := by
    apply ContDiff.sum
    intro k _
    exact hc.comp (contDiff_id.add contDiff_const)
  apply hcont.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.closedBall_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
  exact periodize_eq_finite_sum f N y S (hS y hy)

theorem periodize_no_extra_copies (f : (α → ℝ) → ℂ) (N : α → ℕ) (hN : ∀ i, N i ≠ 0)
    (hsupport : ∀ y, f y ≠ 0 → ∀ i, |y i| < (N i : ℝ) / 2)
    (x : α → ℝ) (hx : ∀ i, |x i| < (N i : ℝ) / 2) : periodize f N x = f x := by
  classical
  have hz : ∀ k : α → ℤ, k ≠ 0 → f (latticeTranslate N k x) = 0 := by
    intro k hk
    have he : ∃ i, k i ≠ 0 := by
      by_contra! h
      exact hk (funext h)
    obtain ⟨i, hi⟩ := he
    by_contra hn
    have hki : (1 : ℝ) ≤ |(k i : ℝ)| := by
      exact_mod_cast (Int.one_le_abs hi)
    have hy := hsupport _ hn i
    have hle : (N i : ℝ) ≤ |(latticeTranslate N k x) i - x i| := by
      simpa [latticeTranslate, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ N i from Nat.cast_nonneg _)] using
        mul_le_mul_of_nonneg_left hki (Nat.cast_nonneg (N i))
    have htri := abs_sub ((latticeTranslate N k x) i) (x i)
    linarith [hx i]
  calc
    periodize f N x = f (latticeTranslate N 0 x) := tsum_eq_single 0 hz
    _ = f x := by congr 1; funext i; simp [latticeTranslate]

end CausalLowerbound.Wiener

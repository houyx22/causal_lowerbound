import CausalLowerbound.CompactIntervalWiener
import CausalLowerbound.PartC.AssignmentDyadic

/-! The actual assignment window in a carrier chart has Wiener norm at
most a constant times its dyadic depth. The constant is independent of
the width and all Fourier realizations agree on the whole unit chart. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators
namespace CausalLowerbound.PartC
open Wiener

def assignmentLayerComplex (x : ℝ) : ℂ := (assignmentLayer x : ℂ)
def assignmentBaseComplex (x : ℝ) : ℂ := (assignmentWindow 1 x : ℂ)

theorem assignmentLayerComplex_smooth : ContDiff ℝ ∞ assignmentLayerComplex :=
  Complex.ofRealCLM.contDiff.comp assignmentLayer_smooth

theorem assignmentBaseComplex_smooth : ContDiff ℝ ∞ assignmentBaseComplex :=
  Complex.ofRealCLM.contDiff.comp (assignmentWindow_smooth 1)

theorem assignmentLayerComplex_compact : HasCompactSupport assignmentLayerComplex :=
  assignmentLayer_compact.comp_left (by simp)

theorem assignmentBaseComplex_compact : HasCompactSupport assignmentBaseComplex :=
  (assignmentWindow_compact 1 (by norm_num)).comp_left (by simp)

theorem assignmentLayerComplex_support (y : ℝ) (hy : assignmentLayerComplex y ≠ 0) : |y| < 1 :=
  assignmentLayer_support y (by simpa [assignmentLayerComplex] using hy)

theorem assignmentBaseComplex_support (y : ℝ) (hy : assignmentBaseComplex y ≠ 0) : |y| < 1 := by
  have hh := assignmentWindow_support 1 y (by norm_num)
    (show assignmentWindow 1 y ≠ 0 by simpa [assignmentBaseComplex] using hy)
  exact abs_lt.mpr (by constructor <;> linarith [hh.1, hh.2])

def assignmentLayerFrequency (j : ℕ) : ℕ := 4 * 2 ^ (j + 1)

theorem assignmentLayerFrequency_ge (j : ℕ) : 4 ≤ assignmentLayerFrequency j := by
  have h : 1 ≤ (2 : ℕ) ^ (j + 1) := Nat.one_le_pow _ _ (by decide)
  unfold assignmentLayerFrequency
  omega

def assignmentLayerWiener (j : ℕ) (a : ℝ) : Fourier (Fin 1) :=
  intervalWiener assignmentLayerComplex assignmentLayerComplex_compact assignmentLayerComplex_smooth
    (assignmentLayerFrequency j) (by have := assignmentLayerFrequency_ge j; omega) a

def assignmentBaseWiener : Fourier (Fin 1) :=
  intervalWiener assignmentBaseComplex assignmentBaseComplex_compact assignmentBaseComplex_smooth
    4 (by decide) (1 / 2)

def assignmentWindowWiener (N : ℕ) : Fourier (Fin 1) :=
  assignmentBaseWiener + ∑ j ∈ Finset.range N,
    (assignmentLayerWiener j (3 / 8) - assignmentLayerWiener j (5 / 8))

theorem assignmentLayerWiener_value (j : ℕ) (a : ℝ) (ha : a ∈ Set.Icc (1 / 4) (3 / 4))
    (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    toContinuous (assignmentLayerWiener j a) (torusProjection (fun _ => x)) =
      (assignmentLayer ((4 * x - 4 * a) / dyadicWidth (j + 1)) : ℂ) := by
  rw [assignmentLayerWiener, intervalWiener_value _ _ _ assignmentLayerComplex_support
    _ (assignmentLayerFrequency_ge j) _ ha _ hx]
  apply congrArg (fun y : ℝ => (assignmentLayer y : ℂ))
  simp only [assignmentLayerFrequency, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
    div_eq_mul_inv, dyadicWidth_inverse]
  ring

theorem assignmentBaseWiener_value (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    toContinuous assignmentBaseWiener (torusProjection (fun _ => x)) =
      (assignmentWindow 1 (4 * x - 2) : ℂ) := by
  rw [assignmentBaseWiener, intervalWiener_value _ _ _ assignmentBaseComplex_support
    _ (by decide) _ (by constructor <;> norm_num) _ hx]
  apply congrArg (fun y : ℝ => (assignmentWindow 1 y : ℂ))
  norm_num <;> ring

theorem assignmentWindowWiener_value (N : ℕ) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    toContinuous (assignmentWindowWiener N) (torusProjection (fun _ => x)) =
      (assignmentWindow (dyadicWidth N) (4 * x - 2) : ℂ) := by
  rw [assignmentWindowWiener, map_add, ContinuousMap.add_apply, assignmentBaseWiener_value x hx]
  simp only [map_sum, map_sub, ContinuousMap.sum_apply, ContinuousMap.sub_apply]
  rw [assignmentWindow_dyadic_sum, Complex.ofReal_add, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [assignmentLayerWiener_value j (3 / 8) (by constructor <;> norm_num) x hx,
    assignmentLayerWiener_value j (5 / 8) (by constructor <;> norm_num) x hx,
    Complex.ofReal_sub]
  congr 2 <;> ring

theorem assignmentWindowWiener_bound : ∃ C ≥ 0, ∀ N : ℕ,
    ‖assignmentWindowWiener N‖ ≤ C * (N + 1) := by
  let B := intervalWienerConstant assignmentBaseComplex
  let L := intervalWienerConstant assignmentLayerComplex
  have hB : 0 ≤ B := intervalWienerConstant_nonneg _ assignmentBaseComplex_compact assignmentBaseComplex_smooth
  have hL : 0 ≤ L := intervalWienerConstant_nonneg _ assignmentLayerComplex_compact assignmentLayerComplex_smooth
  have hb : ‖assignmentBaseWiener‖ ≤ B := intervalWiener_bound _ _ _ _ _ _
  have hl (j : ℕ) (a : ℝ) : ‖assignmentLayerWiener j a‖ ≤ L := intervalWiener_bound _ _ _ _ _ _
  refine ⟨B + 2 * L, by positivity, fun N => ?_⟩
  calc
    _ ≤ ‖assignmentBaseWiener‖ + ‖∑ j ∈ Finset.range N,
        (assignmentLayerWiener j (3 / 8) - assignmentLayerWiener j (5 / 8))‖ := norm_add_le _ _
    _ ≤ B + ∑ j ∈ Finset.range N, (2 * L) := by
      apply add_le_add hb
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj => ?_))
      exact (norm_sub_le _ _).trans (by linarith [hl j (3 / 8), hl j (5 / 8)])
    _ = B + N * (2 * L) := by simp
    _ ≤ (B + 2 * L) * (N + 1) := by nlinarith [mul_nonneg (Nat.cast_nonneg N) hB]

end CausalLowerbound.PartC

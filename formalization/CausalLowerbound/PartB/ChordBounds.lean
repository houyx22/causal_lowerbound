import CausalLowerbound.PartB.FineLocalizedProfiles
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Quantitative chordal geometry on the central lift. These bounds locate
every fine dyadic shell in a fixed Euclidean annulus. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff

namespace CausalLowerbound.PartB.ShellGeometry

theorem abs_sinc_le_one (x : ℝ) : |sinc x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [sinc_of_ne hx, abs_div, div_le_one (abs_pos.mpr hx)]
    exact Real.abs_sin_le_abs

theorem sinc_abs_lower (x : ℝ) (hx : |x| ≤ Real.pi / 2) : 2 / Real.pi ≤ |sinc x| := by
  by_cases h0 : x = 0
  · simp only [h0, sinc_zero, abs_one]
    exact (div_le_one Real.pi_pos).mpr Real.two_le_pi
  · rw [sinc_of_ne h0, abs_div, le_div_iff₀ (abs_pos.mpr h0)]
    exact Real.mul_abs_le_abs_sin hx

variable {d : Type*} [Fintype d]

def euclideanSquare (z : d → ℝ) : ℝ := ∑ i, (z i) ^ 2

theorem euclideanSquare_nonneg (z : d → ℝ) : 0 ≤ euclideanSquare z :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem euclideanSquare_smooth : ContDiff ℝ ∞ (euclideanSquare (d := d)) :=
  ContDiff.sum (fun i _ => (contDiff_apply ℝ ℝ i).pow 2)

theorem radial_abs_upper (τ : ℝ) (z : d → ℝ) (i : d) : |radial τ z i| ≤ 2 * Real.pi * |z i| := by
  rw [radial, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  exact mul_le_of_le_one_right (by positivity) (abs_sinc_le_one _)

theorem radial_abs_lower (τ : ℝ) (z : d → ℝ) (i : d) (hi : |τ * z i| ≤ 1 / 2) :
    4 * |z i| ≤ |radial τ z i| := by
  have hx : |Real.pi * τ * z i| ≤ Real.pi / 2 := by
    rw [mul_assoc, abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have h := mul_le_mul_of_nonneg_left (sinc_abs_lower _ hx)
    (show 0 ≤ 2 * Real.pi * |z i| by positivity)
  rw [radial, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  convert h using 1
  field_simp
  ring

theorem chordSquare_upper (τ : ℝ) (z : d → ℝ) :
    chordSquare τ z ≤ 4 * Real.pi ^ 2 * euclideanSquare z := by
  calc
    _ ≤ ∑ i, (2 * Real.pi * |z i|) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [radial_abs_upper τ z i, abs_nonneg (radial τ z i), abs_nonneg (z i),
        sq_abs (radial τ z i)]
    _ = _ := by
      simp only [mul_pow, sq_abs, euclideanSquare, Finset.mul_sum]
      norm_num

theorem chordSquare_lower (τ : ℝ) (z : d → ℝ) (hz : ∀ i, |τ * z i| ≤ 1 / 2) :
    16 * euclideanSquare z ≤ chordSquare τ z := by
  calc
    _ = ∑ i, (4 * |z i|) ^ 2 := by
      simp only [mul_pow, sq_abs, euclideanSquare, Finset.mul_sum]
      norm_num
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [radial_abs_lower τ z i (hz i), abs_nonneg (radial τ z i),
        abs_nonneg (z i), sq_abs (radial τ z i)]

theorem chordProfile_sq (τ : ℝ) (z : d → ℝ) : (chordProfile τ z) ^ 2 = chordSquare τ z :=
  Real.sq_sqrt (chordSquare_nonneg τ z)

theorem fine_profile_annulus (τ : ℝ) (z : d → ℝ) (hz : ∀ i, |τ * z i| ≤ 1 / 2)
    (hρ : dyadicProfile (chordProfile τ z) ≠ 0) :
    1 / (16 * Real.pi ^ 2) < euclideanSquare z ∧ ∀ i, |z i| < 1 / 2 := by
  have hq := dyadicProfile_support hρ
  have hs := chordProfile_sq τ z
  have hl := chordSquare_lower τ z hz
  have hu := chordSquare_upper τ z
  constructor
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.sq_sqrt (chordSquare_nonneg τ z)]
  · intro i
    have hi : (z i) ^ 2 ≤ euclideanSquare z :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [sq_abs (z i), abs_nonneg (z i)]

end CausalLowerbound.PartB.ShellGeometry

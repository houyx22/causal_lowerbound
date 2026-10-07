import CausalLowerbound.PartB.DyadicCutoffs
import CausalLowerbound.PartB.FineLocalizedProfiles

/-! A concrete smooth nondecreasing truncation of the chordal distance.
It agrees with the distance below 1/16 and is constant above 1/8. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

def distanceCap (r : ℝ) : ℝ := r + (1 / 8 - r) * Real.smoothTransition (16 * r - 1)

theorem distanceCap_smooth : ContDiff ℝ ∞ distanceCap :=
  contDiff_id.add ((contDiff_const.sub contDiff_id).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)))

theorem distanceCap_small {r : ℝ} (hr : r ≤ 1 / 16) : distanceCap r = r := by
  simp only [distanceCap, Real.smoothTransition.zero_of_nonpos (by linarith : 16 * r - 1 ≤ 0),
    mul_zero, add_zero]

theorem distanceCap_large {r : ℝ} (hr : 1 / 8 ≤ r) : distanceCap r = 1 / 8 := by
  rw [distanceCap, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem distanceCap_upper (r : ℝ) : distanceCap r ≤ 1 / 8 := by
  by_cases hr : 1 / 8 ≤ r
  · rw [distanceCap_large hr]
  · have h := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one (16 * r - 1))
      (show 0 ≤ 1 / 8 - r by linarith)
    dsimp [distanceCap]
    nlinarith

theorem distanceCap_lower (r : ℝ) : min r (1 / 8) ≤ distanceCap r := by
  by_cases hr : 1 / 8 ≤ r
  · rw [min_eq_right hr, distanceCap_large hr]
  · rw [min_eq_left (le_of_not_ge hr)]
    exact le_add_of_nonneg_right (mul_nonneg (by linarith) (Real.smoothTransition.nonneg _))

theorem distanceCap_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ distanceCap r :=
  (le_min hr (by norm_num)).trans (distanceCap_lower r)

theorem distanceCap_pos {r : ℝ} (hr : 0 < r) : 0 < distanceCap r :=
  (lt_min hr (by norm_num)).trans_le (distanceCap_lower r)

theorem distanceCap_monotone : Monotone distanceCap := by
  intro x y hxy
  by_cases hy : 1 / 8 ≤ y
  · rw [distanceCap_large hy]
    exact distanceCap_upper x
  · have hx : x ≤ 1 / 8 := by linarith
    have ht := smoothTransition_monotone (show 16 * x - 1 ≤ 16 * y - 1 by linarith)
    have hprod := mul_le_mul (sub_le_sub_left hxy (1 / 8)) (sub_le_sub_left ht 1)
      (sub_nonneg.mpr (Real.smoothTransition.le_one _)) (sub_nonneg.mpr hx)
    dsimp [distanceCap]
    nlinarith

theorem distanceCap_small_value {r : ℝ} (hr : distanceCap r < 1 / 16) :
    r < 1 / 16 ∧ distanceCap r = r := by
  have h : r < 1 / 16 := by
    by_cases hlarge : 1 / 8 ≤ r
    · rw [distanceCap_large hlarge] at hr
      linarith
    · have hh := distanceCap_lower r
      rw [min_eq_left (le_of_not_ge hlarge)] at hh
      linarith
  exact ⟨h, distanceCap_small h.le⟩

theorem distanceCap_le_twice {r : ℝ} (hr : 0 ≤ r) : distanceCap r ≤ 2 * r := by
  by_cases hs : r ≤ 1 / 16
  · rw [distanceCap_small hs]
    linarith
  · linarith [distanceCap_upper r]

variable {d : Type*} [Fintype d]

def chordDistance (u v : d → ℝ) : ℝ :=
  Real.sqrt (∑ a : d × Bool, (embedding u a - embedding v a) ^ 2)

def truncatedDistance (u v : d → ℝ) : ℝ := distanceCap (chordDistance u v)

theorem chordDistance_nonneg (u v : d → ℝ) : 0 ≤ chordDistance u v := Real.sqrt_nonneg _

theorem chordDistance_scale (τ : ℝ) (hτ : 0 ≤ τ) (u z : d → ℝ) :
    chordDistance (fun i => u i + τ * z i) u = τ * chordProfile τ z := by
  rw [chordDistance, embedding_difference_squares, Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hτ]
  rfl

theorem chordDistance_integer_period (u v : d → ℝ) (k l : d → ℤ) :
    chordDistance (fun i => u i + k i) (fun i => v i + l i) = chordDistance u v := by
  simp only [chordDistance, embedding_integer_period]

theorem truncatedDistance_integer_period (u v : d → ℝ) (k l : d → ℤ) :
    truncatedDistance (fun i => u i + k i) (fun i => v i + l i) = truncatedDistance u v := by
  simp only [truncatedDistance, chordDistance_integer_period]

theorem truncatedDistance_range (u v : d → ℝ) : truncatedDistance u v ∈ Set.Icc 0 1 :=
  ⟨distanceCap_nonneg (chordDistance_nonneg u v), (distanceCap_upper _).trans (by norm_num)⟩

theorem fineCutoff_uncapped (m : ℕ) (hm : 5 ≤ m) (u v : d → ℝ)
    (h : fineCutoff m (truncatedDistance u v) ≠ 0) :
    chordDistance u v < 1 / 16 ∧ truncatedDistance u v = chordDistance u v := by
  apply distanceCap_small_value
  have hp : (32 : ℝ) ≤ 2 ^ m := by
    calc
      _ = (2 : ℝ) ^ 5 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hm
  have hh := (fineCutoff_support m (truncatedDistance u v) h).2
  have hd : 2 / (2 : ℝ) ^ m ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  exact hh.trans_le hd

theorem chordDistance_smoothAt (u v : d → ℝ) (h : chordDistance u v ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : (d → ℝ) × (d → ℝ) => chordDistance p.1 p.2) (u, v) := by
  have hd : (∑ a : d × Bool, (embedding u a - embedding v a) ^ 2) ≠ 0 := by
    intro hz
    exact h (by simp [chordDistance, hz])
  have hs : ContDiffAt ℝ ∞ (fun p : (d → ℝ) × (d → ℝ) =>
      ∑ a : d × Bool, (embedding p.1 a - embedding p.2 a) ^ 2) (u, v) := by
    apply ContDiffAt.sum
    intro a _
    exact (((contDiff_embedding a).comp contDiff_fst).contDiffAt.sub
      ((contDiff_embedding a).comp contDiff_snd).contDiffAt).pow 2
  exact hs.sqrt hd

theorem truncatedDistance_smoothAt (u v : d → ℝ) (h : chordDistance u v ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : (d → ℝ) × (d → ℝ) => truncatedDistance p.1 p.2) (u, v) :=
  distanceCap_smooth.contDiffAt.comp (u, v) (chordDistance_smoothAt u v h)

end CausalLowerbound.PartB.ShellGeometry

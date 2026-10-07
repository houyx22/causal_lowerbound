import CausalLowerbound.PartB.TruncatedDistance
import CausalLowerbound.PartB.ChordBounds

/-! Canonical central lifts, rescaled fine-shell coordinates, and exact
identification with the actual truncated-distance shell functions. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

theorem fineCutoff_cap_eq (m : ℕ) (hm : 5 ≤ m) (r : ℝ) :
    fineCutoff m (distanceCap r) = fineCutoff m r := by
  by_cases hr : r ≤ 1 / 16
  · rw [distanceCap_small hr]
  · have hp : (32 : ℝ) ≤ 2 ^ m := by
      have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm
      norm_num at hh ⊢
      exact hh
    have hcap : 1 / 16 ≤ distanceCap r := by
      calc
        _ = distanceCap (1 / 16) := (distanceCap_small le_rfl).symm
        _ ≤ _ := distanceCap_monotone (le_of_not_ge hr)
    have hbase : 2 ≤ (2 : ℝ) ^ m * (1 / 16) := by linarith
    have ha : 2 ≤ (2 : ℝ) ^ m * distanceCap r :=
      hbase.trans (mul_le_mul_of_nonneg_left hcap (by positivity))
    have hb : 2 ≤ (2 : ℝ) ^ m * r :=
      hbase.trans (mul_le_mul_of_nonneg_left (le_of_not_ge hr) (by positivity))
    exact (dyadicProfile_zero_right ha).trans (dyadicProfile_zero_right hb).symm

variable {d : Type*} [Fintype d]

def centralDifference (u v : d → ℝ) : d → ℝ := fun i =>
  u i - v i - (⌊u i - v i + 1 / 2⌋ : ℤ)

def centralShift (u v : d → ℝ) : d → ℤ := fun i => ⌊u i - v i + 1 / 2⌋

theorem centralDifference_bounds (u v : d → ℝ) (i : d) :
    -(1 / 2) ≤ centralDifference u v i ∧ centralDifference u v i < 1 / 2 := by
  have h1 := Int.floor_le (u i - v i + 1 / 2)
  have h2 := Int.lt_floor_add_one (u i - v i + 1 / 2)
  dsimp [centralDifference]
  constructor <;> linarith

theorem centralDifference_abs (u v : d → ℝ) (i : d) : |centralDifference u v i| ≤ 1 / 2 :=
  abs_le.mpr ⟨(centralDifference_bounds u v i).1, (centralDifference_bounds u v i).2.le⟩

theorem centralDifference_decomposition (u v : d → ℝ) :
    u = fun i => (v i + centralDifference u v i) + (centralShift u v i : ℝ) := by
  funext i
  dsimp [centralDifference, centralShift]
  ring

theorem centralDifference_embedding (u v : d → ℝ) :
    embedding (fun i => v i + centralDifference u v i) = embedding u := by
  have h := embedding_integer_period (fun i => v i + centralDifference u v i) (centralShift u v)
  rw [← centralDifference_decomposition] at h
  exact h.symm

theorem chordDistance_central (u v : d → ℝ) :
    chordDistance (fun i => v i + centralDifference u v i) v = chordDistance u v := by
  simp only [chordDistance, centralDifference_embedding]

def fineScale (m : ℕ) : ℝ := ((2 : ℝ) ^ m)⁻¹

def fineLift (m : ℕ) (u v : d → ℝ) : d → ℝ := fun i => (2 : ℝ) ^ m * centralDifference u v i

theorem fineScale_pos (m : ℕ) : 0 < fineScale m := by unfold fineScale; positivity

theorem fineLift_scaled (m : ℕ) (u v : d → ℝ) (i : d) :
    fineScale m * fineLift m u v i = centralDifference u v i := by
  dsimp [fineScale, fineLift]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2 : ℝ) ^ m ≠ 0), one_mul]

theorem fineLift_central (m : ℕ) (u v : d → ℝ) (i : d) :
    |fineScale m * fineLift m u v i| ≤ 1 / 2 := by
  rw [fineLift_scaled]
  exact centralDifference_abs u v i

theorem chordDistance_fineLift (m : ℕ) (u v : d → ℝ) :
    chordDistance u v = fineScale m * chordProfile (fineScale m) (fineLift m u v) := by
  have h := chordDistance_scale (fineScale m) (fineScale_pos m).le v (fineLift m u v)
  simp only [fineLift_scaled, chordDistance_central] at h
  exact h

theorem fineCutoff_profile_exact (m : ℕ) (hm : 5 ≤ m) (u v : d → ℝ) :
    fineCutoff m (truncatedDistance u v) =
      dyadicProfile (chordProfile (fineScale m) (fineLift m u v)) := by
  rw [truncatedDistance, fineCutoff_cap_eq m hm, fineCutoff, chordDistance_fineLift]
  congr 1
  rw [fineScale, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ m ≠ 0), one_mul]

theorem fineLift_annulus (m : ℕ) (hm : 5 ≤ m) (u v : d → ℝ)
    (h : fineCutoff m (truncatedDistance u v) ≠ 0) :
    1 / (16 * Real.pi ^ 2) < euclideanSquare (fineLift m u v) ∧ ∀ i, |fineLift m u v i| < 1 / 2 := by
  apply fine_profile_annulus _ _ (fineLift_central m u v)
  rwa [← fineCutoff_profile_exact m hm]

theorem centralDifference_fine_small (m : ℕ) (hm : 5 ≤ m) (u v : d → ℝ)
    (h : fineCutoff m (truncatedDistance u v) ≠ 0) (i : d) :
    |centralDifference u v i| < 1 / 4 := by
  have hi := (fineLift_annulus m hm u v h).2 i
  have hp : (2 : ℝ) ≤ 2 ^ m := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ m by omega)
  simp only [fineLift, abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ m)] at hi
  have hh := mul_le_mul_of_nonneg_right hp (abs_nonneg (centralDifference u v i))
  nlinarith

/-- Two lifts of the same difference in the small cube must coincide. -/
theorem small_lift_unique (w z : d → ℝ) (k l : d → ℤ)
    (hw : ∀ i, |w i| < 1 / 4) (hz : ∀ i, |z i| < 1 / 4)
    (h : ∀ i, w i + (k i : ℝ) = z i + (l i : ℝ)) : w = z := by
  funext i
  have he : k i = l i := by
    by_contra hn
    have hkl : (1 : ℝ) ≤ |((k i - l i : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hn)
    have ht := abs_sub (z i) (w i)
    have hid : ((k i - l i : ℤ) : ℝ) = z i - w i := by
      rw [Int.cast_sub]
      linarith [h i]
    rw [hid] at hkl
    linarith [hw i, hz i]
  have hi := h i
  rw [he] at hi
  linarith

theorem exists_fine_start (ε : ℝ) (hε : 0 < ε) :
    ∃ m0 : ℕ, 5 ≤ m0 ∧ ∀ m, m0 ≤ m → fineScale m ∈ Set.Icc 0 ε := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / ε) (by norm_num : (1 : ℝ) < 2)
  refine ⟨max 5 n, le_max_left _ _, ?_⟩
  intro m hm
  refine ⟨(fineScale_pos m).le, ?_⟩
  have hp : (2 : ℝ) ^ n ≤ 2 ^ m :=
    pow_le_pow_right₀ (by norm_num) ((le_max_right _ _).trans hm)
  have h := (div_lt_iff₀ hε).mp (hn.trans_le hp)
  rw [fineScale, inv_eq_one_div, div_le_iff₀ (by positivity)]
  nlinarith

end CausalLowerbound.PartB.ShellGeometry

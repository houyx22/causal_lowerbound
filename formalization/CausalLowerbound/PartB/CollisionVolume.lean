import CausalLowerbound.PartB.CentralShellLift
import CausalLowerbound.PartB.PhysicalDesign

/-! Uniform Lebesgue bounds for the actual periodic truncated distance.
The finite covering includes collisions across the boundary of the unit cell. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical ENNReal
open MeasureTheory
namespace CausalLowerbound.PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem centralDifference_le_chord (u v : d → ℝ) (i : d) :
    4 * |centralDifference u v i| ≤ chordDistance u v := by
  have hl := chordSquare_lower 1 (centralDifference u v)
    (fun a => by simpa using centralDifference_abs u v a)
  have he : chordDistance u v = chordProfile 1 (centralDifference u v) := by
    simpa only [one_mul, chordDistance_central] using
      (chordDistance_scale 1 (by norm_num) v (centralDifference u v))
  have hi : (centralDifference u v i) ^ 2 ≤ euclideanSquare (centralDifference u v) :=
    Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hs := chordProfile_sq 1 (centralDifference u v)
  rw [← he] at hs
  nlinarith [abs_nonneg (centralDifference u v i), sq_abs (centralDifference u v i),
    chordDistance_nonneg u v]

def centralShiftOptions (d : Type*) [Fintype d] [DecidableEq d] : Finset (d → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-1) 1)

theorem centralShiftOptions_card : (centralShiftOptions d).card = 3 ^ Fintype.card d := by
  simp [centralShiftOptions, Fintype.card_piFinset]

theorem centralShift_mem_options (u v : d → ℝ)
    (hu : u ∈ Set.Icc (0 : d → ℝ) 1) (hv : v ∈ Set.Icc (0 : d → ℝ) 1) :
    centralShift u v ∈ centralShiftOptions d := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  have h₁ := Int.floor_le (u i - v i + 1 / 2)
  have h₂ := Int.lt_floor_add_one (u i - v i + 1 / 2)
  have hu0 : 0 ≤ u i := hu.1 i
  have hu1 : u i ≤ 1 := hu.2 i
  have hv0 : 0 ≤ v i := hv.1 i
  have hv1 : v i ≤ 1 := hv.2 i
  have hlo : (-2 : ℝ) < (centralShift u v i : ℝ) := by
    dsimp [centralShift]; linarith
  have hhi : (centralShift u v i : ℝ) < 2 := by
    dsimp [centralShift]; linarith
  have hlo' : (-2 : ℤ) < centralShift u v i := by exact_mod_cast hlo
  have hhi' : centralShift u v i < 2 := by exact_mod_cast hhi
  omega

def collisionCube (v : d → ℝ) (k : d → ℤ) (R : ℝ) : Set (d → ℝ) :=
  Set.Icc (fun i => v i + k i - R / 4) (fun i => v i + k i + R / 4)

theorem truncatedDistance_sublevel_cover (v : d → ℝ)
    (hv : v ∈ Set.Icc (0 : d → ℝ) 1) (R : ℝ) (hR : R < 1 / 16) :
    {u | truncatedDistance u v ≤ R} ∩ Set.Icc (0 : d → ℝ) 1 ⊆
      ⋃ k ∈ centralShiftOptions d, collisionCube v k R := by
  rintro u ⟨hu, hcell⟩
  apply Set.mem_iUnion.mpr
  refine ⟨centralShift u v, Set.mem_iUnion.mpr
    ⟨centralShift_mem_options u v hcell hv, ?_⟩⟩
  have he := (distanceCap_small_value (hu.trans_lt hR)).2
  have hb (i : d) : |centralDifference u v i| ≤ R / 4 := by
    have hi := centralDifference_le_chord u v i
    change distanceCap (chordDistance u v) ≤ R at hu
    rw [he] at hu
    linarith
  constructor <;> intro i
  · have := (abs_le.mp (hb i)).1
    dsimp [centralDifference, centralShift] at *
    linarith
  · have := (abs_le.mp (hb i)).2
    dsimp [centralDifference, centralShift] at *
    linarith

theorem collisionCube_volume (v : d → ℝ) (k : d → ℤ) (R : ℝ) :
    volume (collisionCube v k R) = ENNReal.ofReal (R / 2) ^ Fintype.card d := by
  simp only [collisionCube, Real.volume_Icc_pi]
  have he (i : d) : v i + k i + R / 4 - (v i + k i - R / 4) = R / 2 := by ring
  simp only [he, Finset.prod_const, Finset.card_univ]

theorem truncatedDistance_sublevel_volume (v : d → ℝ)
    (hv : v ∈ Set.Icc (0 : d → ℝ) 1) (R : ℝ) (hR : R < 1 / 16) :
    cubeMeasure d {u | truncatedDistance u v ≤ R} ≤
      ENNReal.ofReal (3 * R / 2) ^ Fintype.card d := by
  rw [cubeMeasure, Measure.restrict_apply' measurableSet_Icc]
  calc
    _ ≤ volume (⋃ k ∈ centralShiftOptions d, collisionCube v k R) :=
      measure_mono (truncatedDistance_sublevel_cover v hv R hR)
    _ ≤ ∑ k ∈ centralShiftOptions d, volume (collisionCube v k R) :=
      measure_biUnion_finset_le _ _
    _ = _ := by
      simp only [collisionCube_volume, Finset.sum_const, centralShiftOptions_card,
        nsmul_eq_mul, Nat.cast_pow]
      rw [← mul_pow]
      congr 1
      change (3 : ℝ≥0∞) * ENNReal.ofReal (R / 2) = _
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      ring

theorem truncatedDistance_sublevel_real_volume (v : d → ℝ)
    (hv : v ∈ Set.Icc (0 : d → ℝ) 1) (R : ℝ) (hR0 : 0 ≤ R) (hR : R < 1 / 16) :
    (cubeMeasure d).real {u | truncatedDistance u v ≤ R} ≤ (3 * R / 2) ^ Fintype.card d := by
  have h := ENNReal.toReal_mono (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (truncatedDistance_sublevel_volume v hv R hR)
  simpa [measureReal_def, ENNReal.toReal_pow, ENNReal.toReal_ofReal (show 0 ≤ 3 * R / 2 by positivity)] using h

theorem truncatedDistance_zero_null [Nonempty d] (v : d → ℝ)
    (hv : v ∈ Set.Icc (0 : d → ℝ) 1) :
    cubeMeasure d {u | truncatedDistance u v = 0} = 0 := by
  apply le_antisymm _ (zero_le _)
  calc
    _ ≤ cubeMeasure d {u | truncatedDistance u v ≤ 0} := measure_mono (by intro u hu; exact hu.le)
    _ ≤ ENNReal.ofReal (3 * 0 / 2) ^ Fintype.card d :=
      truncatedDistance_sublevel_volume v hv 0 (by norm_num)
    _ = 0 := by simp [Fintype.card_ne_zero]

/-- A single bound valid at all positive radii, convenient for moment estimates. -/
theorem truncatedDistance_sublevel_global (v : d → ℝ)
    (hv : v ∈ Set.Icc (0 : d → ℝ) 1) (R : ℝ) (hR : 0 < R) :
    cubeMeasure d {u | truncatedDistance u v ≤ R} ≤
      ENNReal.ofReal ((16 * R) ^ Fintype.card d) := by
  by_cases hs : R < 1 / 16
  · calc
      _ ≤ ENNReal.ofReal (3 * R / 2) ^ Fintype.card d :=
        truncatedDistance_sublevel_volume v hv R hs
      _ ≤ ENNReal.ofReal (16 * R) ^ Fintype.card d := by
        gcongr
        linarith
      _ = _ := (ENNReal.ofReal_pow (by positivity) _).symm
  · have hr : 1 ≤ 16 * R := by linarith
    calc
      _ ≤ 1 := prob_le_one
      _ = ENNReal.ofReal 1 := by norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal (one_le_pow₀ hr)

end CausalLowerbound.PartB.ShellGeometry

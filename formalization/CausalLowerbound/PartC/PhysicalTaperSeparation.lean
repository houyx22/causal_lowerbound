import CausalLowerbound.PartC.PhysicalPropensityShift
import CausalLowerbound.PartB.FiniteShellPartition
import CausalLowerbound.PartB.ChordBounds
import CausalLowerbound.PartB.CompleteGraph

/-! The nonzero complete taper separates actual physical rough packets.
A global upper bound on chordal distance suffices; no central lift or
interior chart assumption is needed. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry ConfigurationShells
variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [LinearOrder V]

def physicalChartDistanceConstant (d : Type*) [Fintype d] : ℝ :=
  4 * Real.pi * ((Fintype.card d : ℝ) + 1)

omit [DecidableEq d] in
theorem physicalChartDistanceConstant_pos : 0 < physicalChartDistanceConstant d := by
  unfold physicalChartDistanceConstant
  positivity

omit [DecidableEq d] in
theorem truncatedDistance_le_chartDistanceConstant (u v : d → ℝ) :
    truncatedDistance u v ≤ physicalChartDistanceConstant d * ‖u - v‖ := by
  have he : (fun i => v i + 1 * (u - v) i) = u := by
    funext i
    simp only [Pi.sub_apply, one_mul]
    ring
  have hc : chordDistance u v = chordProfile 1 (u - v) := by
    have hh := chordDistance_scale 1 (by norm_num) v (u - v)
    rw [he, one_mul] at hh
    exact hh
  have hs : euclideanSquare (u - v) ≤ (((Fintype.card d : ℝ) + 1) * ‖u - v‖) ^ 2 := by
    calc
      _ ≤ ∑ _i : d, ‖u - v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi : |(u - v) i| ≤ ‖u - v‖ := by
          simpa only [Real.norm_eq_abs] using norm_le_pi_norm (u - v) i
        nlinarith [sq_abs ((u - v) i), abs_nonneg ((u - v) i), norm_nonneg (u - v)]
      _ = (Fintype.card d : ℝ) * ‖u - v‖ ^ 2 := by simp
      _ ≤ ((Fintype.card d : ℝ) + 1) ^ 2 * ‖u - v‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have hd := Nat.cast_nonneg (α := ℝ) (Fintype.card d)
        nlinarith
      _ = _ := by ring
  have hsq : chordDistance u v ^ 2 ≤
      (2 * Real.pi * (((Fintype.card d : ℝ) + 1) * ‖u - v‖)) ^ 2 := by
    calc
      _ = chordSquare 1 (u - v) := by rw [hc, chordProfile_sq]
      _ ≤ 4 * Real.pi ^ 2 * euclideanSquare (u - v) := chordSquare_upper 1 (u - v)
      _ ≤ 4 * Real.pi ^ 2 * ((((Fintype.card d : ℝ) + 1) * ‖u - v‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have hb : chordDistance u v ≤ 2 * Real.pi * (((Fintype.card d : ℝ) + 1) * ‖u - v‖) := by
    have hp : 0 ≤ 2 * Real.pi * (((Fintype.card d : ℝ) + 1) * ‖u - v‖) := by positivity
    nlinarith [chordDistance_nonneg u v]
  calc
    _ ≤ 2 * chordDistance u v := distanceCap_le_twice (chordDistance_nonneg u v)
    _ ≤ 2 * (2 * Real.pi * (((Fintype.card d : ℝ) + 1) * ‖u - v‖)) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by unfold physicalChartDistanceConstant; ring

omit [Fintype d] [DecidableEq d] in
theorem roughChartPoint_sub (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) (u v : d → ℝ) :
    roughChartPoint x₀ r k u - roughChartPoint x₀ r k v = (4 * r) • (u - v) := by
  funext i
  simp only [roughChartPoint, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem roughChartPoint_distance (x₀ : d → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (k : d → ℤ) (u v : d → ℝ) :
    ‖roughChartPoint x₀ r k u - roughChartPoint x₀ r k v‖ = 4 * r * ‖u - v‖ := by
  rw [roughChartPoint_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

omit [DecidableEq d] in
theorem taper_nonzero_pair_lower (u : V × d → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hχ : graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) ≠ 0)
    (i j : V) (hij : i ≠ j) :
    τ < truncatedDistance (configurationSite u i) (configurationSite u j) := by
  have he (a b : V) (hab : a < b) :
      τ < truncatedDistance (configurationSite u a) (configurationSite u b) :=
    taper_nonzero_edge_lower edgeLeft edgeRight τ hτ (graphDistance edgeLeft edgeRight u)
      (fun e => truncatedDistance_range _ _) hχ (⟨(a, b), hab⟩ : CompleteEdge V)
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact he i j hij
  · simpa only [truncatedDistance_symm] using he j i hij

theorem taper_nonzero_physical_separation (x₀ : d → ℝ) (ℓ r : ℝ) (hr : 0 < r)
    (k : d → ℤ) (u : V × d → ℝ) (τ : ℝ) (hτ : 0 < τ)
    (hscale : 2 * physicalChartDistanceConstant d * ℓ ≤ 4 * r * τ)
    (hχ : graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) ≠ 0) :
    ∀ i j, i ≠ j → 2 * ℓ <
      ‖roughChartPoint x₀ r k (configurationSite u i) - roughChartPoint x₀ r k (configurationSite u j)‖ := by
  intro i j hij
  have hp := (taper_nonzero_pair_lower u τ hτ hχ i j hij).trans_le
    (truncatedDistance_le_chartDistanceConstant (configurationSite u i) (configurationSite u j))
  have hm : physicalChartDistanceConstant d * (2 * ℓ) < physicalChartDistanceConstant d *
      ‖roughChartPoint x₀ r k (configurationSite u i) - roughChartPoint x₀ r k (configurationSite u j)‖ := by
    calc
      _ = 2 * physicalChartDistanceConstant d * ℓ := by ring
      _ ≤ 4 * r * τ := hscale
      _ < 4 * r * (physicalChartDistanceConstant d * ‖configurationSite u i - configurationSite u j‖) :=
        mul_lt_mul_of_pos_left hp (by positivity)
      _ = _ := by rw [roughChartPoint_distance x₀ r hr.le]; ring
  exact (mul_lt_mul_left physicalChartDistanceConstant_pos).mp hm

end CausalLowerbound.PartC

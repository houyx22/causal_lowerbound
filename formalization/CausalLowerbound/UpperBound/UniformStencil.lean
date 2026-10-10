import CausalLowerbound.UpperBound.TensorGrid
import Mathlib.Analysis.Normed.Ring.Units

/-! Positive-volume node boxes with a uniform inverse bound.  The reference
grid is explicit; continuity produces one radius valid for every simultaneous
selection of a node from every box. -/

noncomputable section
set_option autoImplicit false
open Filter Set
open scoped BigOperators Topology Matrix Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

def inverseEntryBudget (p : ℕ) (z : TensorIndex d p → d → ℝ) : ℝ :=
  ∑ i, ∑ j, |(tensorEvaluation p z)⁻¹ i j|

theorem inverseEntryBudget_nonneg (p : ℕ) (z : TensorIndex d p → d → ℝ) :
    0 ≤ inverseEntryBudget p z :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg ((tensorEvaluation p z)⁻¹ i j)

theorem inverse_row_le_budget (p : ℕ) (z : TensorIndex d p → d → ℝ)
    (i : TensorIndex d p) :
    (∑ j, |(tensorEvaluation p z)⁻¹ i j|) ≤ inverseEntryBudget p z := by
  exact Finset.single_le_sum (f := fun k : TensorIndex d p => ∑ j, |(tensorEvaluation p z)⁻¹ k j|)
    (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg ((tensorEvaluation p z)⁻¹ k j))
    (Finset.mem_univ i)

theorem continuousAt_tensorEvaluation_inv (p : ℕ) (z : TensorIndex d p → d → ℝ)
    (hz : IsUnit (tensorEvaluation p z).det) :
    ContinuousAt (fun w => (tensorEvaluation p w)⁻¹) z := by
  classical
  obtain ⟨u, hu⟩ := hz
  have hi : ContinuousAt Ring.inverse (tensorEvaluation p z).det := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  exact (continuousAt_matrix_inv _ hi).comp (continuous_tensorEvaluation p).continuousAt

theorem continuousAt_inverseEntryBudget (p : ℕ) (z : TensorIndex d p → d → ℝ)
    (hz : IsUnit (tensorEvaluation p z).det) : ContinuousAt (inverseEntryBudget p) z := by
  have hs : Continuous (fun A : Matrix (TensorIndex d p) (TensorIndex d p) ℝ =>
      ∑ i, ∑ j, |A i j|) := by fun_prop
  exact hs.continuousAt.comp (continuousAt_tensorEvaluation_inv p z hz)

theorem positive_grid_eventually (p : ℕ) :
    ∀ᶠ z in 𝓝 (gridNode (d := d) p), ∀ j i, 0 < z j i ∧ z j i < 1 := by
  apply Filter.eventually_all.mpr
  intro j
  apply Filter.eventually_all.mpr
  intro i
  have hc : Continuous (fun z : TensorIndex d p → d → ℝ => z j i) := by fun_prop
  exact hc.continuousAt.eventually
    (isOpen_Ioo.mem_nhds ⟨gridCoordinate_pos p (j i), gridCoordinate_lt_one p (j i)⟩)

/-- A single fixed radius controls positivity, nonsingularity, and every
inverse row for all choices of auxiliary nodes in the resulting boxes. -/
theorem exists_uniform_positive_stencil (p : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ z : TensorIndex d p → d → ℝ,
        (∀ j i, |z j i - gridNode p j i| ≤ δ) →
          (∀ j i, 0 < z j i ∧ z j i < 1) ∧
          IsUnit (tensorEvaluation p z).det ∧
          ∀ i, ∑ j, |(tensorEvaluation p z)⁻¹ i j| ≤ C := by
  classical
  let z₀ := gridNode (d := d) p
  let C := inverseEntryBudget p z₀ + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith [inverseEntryBudget_nonneg p z₀]
  have hunit := tensorEvaluation_grid_isUnit_det (d := d) p
  have hdet : ∀ᶠ z in 𝓝 z₀, IsUnit (tensorEvaluation p z).det := by
    have hc := (continuous_tensorEvaluation (d := d) p).matrix_det.continuousAt (x := z₀)
    have hh := hc.eventually
      (isOpen_ne.mem_nhds (show (tensorEvaluation p z₀).det ≠ 0 from isUnit_iff_ne_zero.mp hunit))
    exact hh.mono fun z hz => isUnit_iff_ne_zero.mpr hz
  have hbudget : ∀ᶠ z in 𝓝 z₀, inverseEntryBudget p z < C :=
    (continuousAt_inverseEntryBudget p z₀ hunit).eventually
      (isOpen_Iio.mem_nhds (show inverseEntryBudget p z₀ < C by dsimp [C]; linarith))
  have he : ∀ᶠ z in 𝓝 z₀,
      (∀ j i, 0 < z j i ∧ z j i < 1) ∧
        IsUnit (tensorEvaluation p z).det ∧ inverseEntryBudget p z < C :=
    (positive_grid_eventually p).and (hdet.and hbudget)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε / 2, C, by positivity, hC, ?_⟩
  intro z hz
  have hdist : dist z z₀ ≤ ε / 2 := by
    apply (dist_pi_le_iff (by positivity)).mpr
    intro j
    apply (dist_pi_le_iff (by positivity)).mpr
    intro i
    simpa only [Real.dist_eq, z₀] using hz j i
  have hh := hball (lt_of_le_of_lt hdist (by linarith))
  exact ⟨hh.1, hh.2.1, fun i => (inverse_row_le_budget p z i).trans hh.2.2.le⟩

end CausalLowerbound.UpperBound

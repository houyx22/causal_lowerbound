import CausalLowerbound.DiscreteBayes
import CausalLowerbound.PartB.PhysicalJointComparison

/-! The actual iid covariate density and its positive countable mixture. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def designSampleDensity (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (labels : S → ℕ)
    (x₀ : d → ℝ) (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) : ℝ :=
  ∏ i, normalizedDesign Q S θ (extendLabels S labels) x₀ r (x i)

theorem designSampleDensity_measurable (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (labels : S → ℕ) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) :
    Measurable (designSampleDensity Q S θ labels x₀ r (n := n)) :=
  Finset.measurable_prod _ (fun i _ =>
    (normalizedDesign_legal Q S θ hθ hθ1 (extendLabels S labels) x₀ r).1.comp (measurable_pi_apply i))

theorem designSampleDensity_bounds (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (labels : S → ℕ) (x₀ : d → ℝ) (r : ℝ)
    {n : ℕ} (x : Fin n → d → ℝ) :
    (((1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d)) ^ n ≤
      designSampleDensity Q S θ labels x₀ r x) ∧
    (designSampleDensity Q S θ labels x₀ r x ≤
      ((1 + θ) ^ (5 ^ Fintype.card d) / (1 - θ) ^ (5 ^ Fintype.card d)) ^ n) := by
  have hl : 0 ≤ (1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d) :=
    div_nonneg (pow_nonneg (sub_nonneg.mpr hθ1.le) _) (by positivity)
  have hf := (normalizedDesign_legal Q S θ hθ hθ1 (extendLabels S labels) x₀ r).2.2
  constructor
  · simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin n =>
        (1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d))
        (fun _ _ => hl) (fun i _ => (hf (x i)).1))
  · simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod (s := Finset.univ) (f := fun i : Fin n => normalizedDesign Q S θ (extendLabels S labels) x₀ r (x i))
        (fun i _ => hl.trans (hf (x i)).1) (fun i _ => (hf (x i)).2))

theorem designSampleDensity_pos (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (labels : S → ℕ) (x₀ : d → ℝ) (r : ℝ)
    {n : ℕ} (x : Fin n → d → ℝ) : 0 < designSampleDensity Q S θ labels x₀ r x :=
  (pow_pos (div_pos (pow_pos (sub_pos.mpr hθ1) _) (pow_pos (by linarith) _)) n).trans_le
    (designSampleDensity_bounds Q S θ hθ hθ1 labels x₀ r x).1

theorem designSampleMeasure_density (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (labels : S → ℕ) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) :
    designSampleMeasure Q S θ labels x₀ r n =
      (Measure.pi (fun _ : Fin n => cubeMeasure d)).withDensity
        (fun x => ENNReal.ofReal (designSampleDensity Q S θ labels x₀ r x)) := by
  letI := designMeasure_probability Q S θ hθ hθ1 (extendLabels S labels) x₀ r
  exact finiteProduct_withDensity (fun _ : Fin n => cubeMeasure d)
    (fun _ => normalizedDesign Q S θ (extendLabels S labels) x₀ r)
    (fun _ => (design_integrable Q S θ hθ hθ1 (extendLabels S labels) x₀ r).div_const _)
    (fun _ x => (div_nonneg (pow_nonneg (sub_nonneg.mpr hθ1.le) _) (by positivity)).trans
      ((normalizedDesign_legal Q S θ hθ hθ1 (extendLabels S labels) x₀ r).2.2 x).1)

theorem mixedDesign_density_pos {Ω : Type*} [Fintype Ω]
    (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω) (x₀ : d → ℝ) (r : ℝ)
    {n : ℕ} (x : Fin n → d → ℝ) :
    0 < (tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r n).expect
      (fun z => designSampleDensity Q S θ z.1 x₀ r x) := by
  have hl : 0 < ((1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d)) ^ n :=
    pow_pos (div_pos (pow_pos (sub_pos.mpr hθ1) _) (pow_pos (by linarith) _)) n
  exact hl.trans_le ((tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r n).expect_bounds _ _ _ hl.le
    (fun z => designSampleDensity_bounds Q S θ hθ hθ1 z.1 x₀ r x)).1

end CausalLowerbound.PartB.ShellGeometry

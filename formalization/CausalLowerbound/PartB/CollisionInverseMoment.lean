import CausalLowerbound.PartB.CollisionVolume
import CausalLowerbound.TailMoment

/-! Negative moments of the actual periodic distance, uniformly in the
root site. Every exponent below the dimension is allowed. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
namespace CausalLowerbound.PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def collisionInverseMoment (s : ℝ) (v u : d → ℝ) : ℝ :=
  truncatedDistance u v ^ (-s)

theorem collisionInverseMoment_measurable (s : ℝ) (v : d → ℝ) :
    Measurable (collisionInverseMoment s v) :=
  (truncatedDistance_continuous.comp (continuous_id.prodMk continuous_const)).measurable.pow_const _

theorem collisionInverseMoment_nonneg (s : ℝ) (v u : d → ℝ) :
    0 ≤ collisionInverseMoment s v u := Real.rpow_nonneg (truncatedDistance_range u v).1 _

theorem collisionInverseMoment_tail (s : ℝ) (hs : 0 < s) (v : d → ℝ)
    (hv : v ∈ Set.Icc (0 : d → ℝ) 1) (t : ℝ) (ht : 0 < t) :
    cubeMeasure d {u | t < collisionInverseMoment s v u} ≤
      ENNReal.ofReal ((16 : ℝ) ^ Fintype.card d * t ^ (-(Fintype.card d : ℝ) / s)) := by
  have hsub : {u | t < collisionInverseMoment s v u} ⊆
      {u | truncatedDistance u v ≤ t ^ (-s)⁻¹} := by
    intro u hu
    change t < collisionInverseMoment s v u at hu
    have hd : 0 < truncatedDistance u v := by
      apply lt_of_le_of_ne (truncatedDistance_range u v).1
      intro hz
      have hzero : collisionInverseMoment s v u = 0 := by
        simp [collisionInverseMoment, ← hz, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
      rw [hzero] at hu
      linarith
    exact ((Real.lt_rpow_inv_iff_of_neg hd ht (neg_neg_of_pos hs)).mpr hu).le
  calc
    _ ≤ cubeMeasure d {u | truncatedDistance u v ≤ t ^ (-s)⁻¹} := measure_mono hsub
    _ ≤ ENNReal.ofReal ((16 * t ^ (-s)⁻¹) ^ Fintype.card d) :=
      truncatedDistance_sublevel_global v hv _ (Real.rpow_pos_of_pos ht _)
    _ = _ := by
      congr 1
      rw [mul_pow, ← Real.rpow_natCast (t ^ (-s)⁻¹), ← Real.rpow_mul ht.le]
      congr 2
      field_simp [hs.ne']

def collisionMomentBound (d : Type*) [Fintype d] (s : ℝ) : ℝ :=
  tailMomentBound ((16 : ℝ) ^ Fintype.card d) ((Fintype.card d : ℝ) / s)

theorem collisionMomentBound_nonneg (s : ℝ) : 0 ≤ collisionMomentBound d s :=
  tailMomentBound_nonneg _ _ (by positivity)

theorem collisionInverseMoment_integrable (s : ℝ) (hs : 0 < s)
    (hsd : s < (Fintype.card d : ℝ)) (v : d → ℝ)
    (hv : v ∈ Set.Icc (0 : d → ℝ) 1) :
    Integrable (collisionInverseMoment s v) (cubeMeasure d) ∧
      (∫ u, collisionInverseMoment s v u ∂cubeMeasure d) ≤ collisionMomentBound d s := by
  apply integrable_of_power_tail (cubeMeasure d) _
    (collisionInverseMoment_measurable s v) (collisionInverseMoment_nonneg s v)
    ((16 : ℝ) ^ Fintype.card d) ((Fintype.card d : ℝ) / s) (by positivity)
    ((one_lt_div hs).mpr hsd)
  intro t ht
  simpa only [neg_div] using collisionInverseMoment_tail s hs v hv t (by linarith)

end CausalLowerbound.PartB.ShellGeometry

import CausalLowerbound.PartB.ShellGeometry
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Compact

/-! Nonvanishing denominators, exact Lagrange quotients, and uniform derivatives
for the fine-shell profiles of the explicit torus embedding. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators Topology

namespace CausalLowerbound.PartB.ShellGeometry

variable {d : Type*} [Fintype d]

theorem chordSquare_nonneg (τ : ℝ) (z : d → ℝ) : 0 ≤ chordSquare τ z :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem chordSquare_pos (τ : ℝ) (z : d → ℝ) (hz : z ≠ 0)
    (hsmall : ∀ i, |τ * z i| < 1) : 0 < chordSquare τ z := by
  classical
  have he : ∃ i, z i ≠ 0 := by
    by_contra! h
    exact hz (funext h)
  obtain ⟨i, hi⟩ := he
  have harg : |Real.pi * τ * z i| < Real.pi := by
    rw [mul_assoc, abs_mul, abs_of_pos Real.pi_pos]
    simpa using mul_lt_mul_of_pos_left (hsmall i) Real.pi_pos
  have hr : radial τ z i ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hi) (sinc_ne_zero harg)
  exact (sq_pos_of_ne_zero hr).trans_le
    (Finset.single_le_sum (fun j _ => sq_nonneg (radial τ z j)) (Finset.mem_univ i))

theorem differenceProfile_squares (τ : ℝ) (u z : d → ℝ) :
    (∑ a, (differenceProfile τ u z a) ^ 2) = chordSquare τ z := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fintype.sum_bool, differenceProfile, Bool.false_eq_true, ↓reduceIte, mul_pow, neg_sq]
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * u i + Real.pi * τ * z i)]

theorem embedding_difference_squares (τ : ℝ) (u z : d → ℝ) :
    (∑ a, (embedding (fun i => u i + τ * z i) a - embedding u a) ^ 2) =
      τ ^ 2 * chordSquare τ z := by
  simp_rw [← differenceProfile_mul_scale, mul_pow]
  rw [← Finset.mul_sum, differenceProfile_squares]

theorem coefficientProfile_exact (τ : ℝ) (u z : d → ℝ) (hτ : τ ≠ 0) (a : d × Bool) :
    coefficientProfile τ u z a =
      τ * ((embedding (fun i => u i + τ * z i) a - embedding u a) /
        ∑ b, (embedding (fun i => u i + τ * z i) b - embedding u b) ^ 2) := by
  rw [embedding_difference_squares, ← differenceProfile_mul_scale, coefficientProfile]
  by_cases hD : chordSquare τ z = 0
  · simp [hD]
  · field_simp; ring

theorem constantProfile_exact (τ : ℝ) (u z : d → ℝ) (hτ : τ ≠ 0) :
    constantProfile τ u z =
      τ * ((∑ a, embedding u a * (embedding (fun i => u i + τ * z i) a - embedding u a)) /
        ∑ b, (embedding (fun i => u i + τ * z i) b - embedding u b) ^ 2) := by
  rw [embedding_difference_squares]
  simp_rw [← differenceProfile_mul_scale, mul_left_comm (embedding u _)]
  rw [← Finset.mul_sum, constantProfile]
  by_cases hD : chordSquare τ z = 0
  · simp [hD]
  · field_simp; ring

theorem contDiff_radial (i : d) :
    ContDiff ℝ ∞ (fun p : ℝ × (d → ℝ) => radial p.1 p.2 i) := by
  unfold radial
  have hz : ContDiff ℝ ∞ (fun p : ℝ × (d → ℝ) => p.2 i) :=
    (contDiff_apply ℝ ℝ i).comp contDiff_snd
  exact (contDiff_const.mul hz).mul
    (contDiff_sinc.comp ((contDiff_const.mul contDiff_fst).mul hz))

theorem contDiff_chordSquare :
    ContDiff ℝ ∞ (fun p : ℝ × (d → ℝ) => chordSquare p.1 p.2) := by
  unfold chordSquare
  exact ContDiff.sum (fun i _ => (contDiff_radial i).pow 2)

theorem contDiff_embedding (a : d × Bool) : ContDiff ℝ ∞ (fun u => embedding u a) := by
  unfold embedding
  split_ifs
  · exact Real.contDiff_sin.comp (contDiff_const.mul (contDiff_apply ℝ ℝ a.1))
  · exact Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ a.1))

theorem contDiff_differenceProfile (a : d × Bool) :
    ContDiff ℝ ∞ (fun p : ℝ × ((d → ℝ) × (d → ℝ)) => differenceProfile p.1 p.2.1 p.2.2 a) := by
  unfold differenceProfile
  apply ContDiff.mul
  · exact (contDiff_radial a.1).comp (contDiff_fst.prodMk contDiff_snd.snd)
  · have hu : ContDiff ℝ ∞ (fun p : ℝ × ((d → ℝ) × (d → ℝ)) => p.2.1 a.1) :=
      (contDiff_apply ℝ ℝ a.1).comp contDiff_snd.fst
    have hz : ContDiff ℝ ∞ (fun p : ℝ × ((d → ℝ) × (d → ℝ)) => p.2.2 a.1) :=
      (contDiff_apply ℝ ℝ a.1).comp contDiff_snd.snd
    have harg : ContDiff ℝ ∞ (fun p : ℝ × ((d → ℝ) × (d → ℝ)) =>
        2 * Real.pi * p.2.1 a.1 + Real.pi * p.1 * p.2.2 a.1) :=
      (contDiff_const.mul hu).add ((contDiff_const.mul contDiff_fst).mul hz)
    split_ifs
    · exact Real.contDiff_cos.comp harg
    · exact (Real.contDiff_sin.comp harg).neg

theorem contDiffAt_coefficientProfile (τ : ℝ) (u z : d → ℝ) (a : d × Bool)
    (hD : chordSquare τ z ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ((d → ℝ) × (d → ℝ)) => coefficientProfile p.1 p.2.1 p.2.2 a)
      (τ, u, z) := by
  exact (contDiff_differenceProfile a).contDiffAt.div
    (contDiff_chordSquare.comp (contDiff_fst.prodMk contDiff_snd.snd)).contDiffAt hD

theorem contDiffAt_constantProfile (τ : ℝ) (u z : d → ℝ) (hD : chordSquare τ z ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ((d → ℝ) × (d → ℝ)) => constantProfile p.1 p.2.1 p.2.2)
      (τ, u, z) := by
  apply ContDiffAt.div
  · apply ContDiffAt.sum
    intro a _
    exact ((contDiff_embedding a).comp contDiff_snd.fst).contDiffAt.mul
      (contDiff_differenceProfile a).contDiffAt
  · exact (contDiff_chordSquare.comp (contDiff_fst.prodMk contDiff_snd.snd)).contDiffAt
  · exact hD

theorem contDiffAt_chordProfile (τ : ℝ) (z : d → ℝ) (hD : chordSquare τ z ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (d → ℝ) => chordProfile p.1 p.2) (τ, z) :=
  contDiff_chordSquare.contDiffAt.sqrt hD

end CausalLowerbound.PartB.ShellGeometry

import CausalLowerbound.PartB.CentralShellLift
import CausalLowerbound.PartB.AnnularCutoff

/-! The actual elementary Lagrange coefficients and their exact rescaling.
The constant coefficient here has the unsigned convention of the paper's
list of elementary multipliers; the interpolation polynomial uses its negative. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

variable {d : Type*} [Fintype d]

def pairDenominator (u v : d → ℝ) : ℝ := ∑ a : d × Bool, (embedding u a - embedding v a) ^ 2

def elementaryCoefficient (u v : d → ℝ) (a : Option (d × Bool)) : ℝ :=
  match a with
  | none => (∑ b, embedding v b * (embedding u b - embedding v b)) / pairDenominator u v
  | some b => (embedding u b - embedding v b) / pairDenominator u v

theorem pairDenominator_smooth :
    ContDiff ℝ ∞ (fun p : (d → ℝ) × (d → ℝ) => pairDenominator p.1 p.2) := by
  apply ContDiff.sum
  intro a _
  exact (((contDiff_embedding a).comp contDiff_fst).sub
    ((contDiff_embedding a).comp contDiff_snd)).pow 2

theorem chordDistance_continuous :
    Continuous (fun p : (d → ℝ) × (d → ℝ) => chordDistance p.1 p.2) :=
  Real.continuous_sqrt.comp pairDenominator_smooth.continuous

theorem truncatedDistance_continuous :
    Continuous (fun p : (d → ℝ) × (d → ℝ) => truncatedDistance p.1 p.2) :=
  distanceCap_smooth.continuous.comp chordDistance_continuous

theorem pairDenominator_symm (u v : d → ℝ) : pairDenominator u v = pairDenominator v u := by
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem chordDistance_symm (u v : d → ℝ) : chordDistance u v = chordDistance v u :=
  congrArg Real.sqrt (pairDenominator_symm u v)

theorem truncatedDistance_symm (u v : d → ℝ) : truncatedDistance u v = truncatedDistance v u :=
  congrArg distanceCap (chordDistance_symm u v)

theorem pairDenominator_ne_zero (u v : d → ℝ) (h : chordDistance u v ≠ 0) : pairDenominator u v ≠ 0 := by
  intro hz
  exact h (by change Real.sqrt (pairDenominator u v) = 0; rw [hz, Real.sqrt_zero])

theorem elementaryCoefficient_smoothAt (u v : d → ℝ) (a : Option (d × Bool))
    (h : chordDistance u v ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : (d → ℝ) × (d → ℝ) => elementaryCoefficient p.1 p.2 a) (u, v) := by
  have hd := pairDenominator_ne_zero u v h
  cases a with
  | none =>
    have hn : ContDiffAt ℝ ∞ (fun p : (d → ℝ) × (d → ℝ) =>
        ∑ b, embedding p.2 b * (embedding p.1 b - embedding p.2 b)) (u, v) := by
      apply ContDiffAt.sum
      intro b _
      exact ((contDiff_embedding b).comp contDiff_snd).contDiffAt.mul
        (((contDiff_embedding b).comp contDiff_fst).contDiffAt.sub
          ((contDiff_embedding b).comp contDiff_snd).contDiffAt)
    exact hn.div pairDenominator_smooth.contDiffAt hd
  | some a =>
    exact (((contDiff_embedding a).comp contDiff_fst).contDiffAt.sub
      ((contDiff_embedding a).comp contDiff_snd).contDiffAt).div pairDenominator_smooth.contDiffAt hd

theorem elementaryCoefficient_embedding_eq (u v u' v' : d → ℝ)
    (hu : embedding u = embedding u') (hv : embedding v = embedding v') (a : Option (d × Bool)) :
    elementaryCoefficient u v a = elementaryCoefficient u' v' a := by
  cases a <;> simp only [elementaryCoefficient, pairDenominator, hu, hv]

theorem elementaryCoefficient_integer_period (u v : d → ℝ) (k l : d → ℤ) (a : Option (d × Bool)) :
    elementaryCoefficient (fun i => u i + k i) (fun i => v i + l i) a = elementaryCoefficient u v a :=
  elementaryCoefficient_embedding_eq _ _ _ _ (embedding_integer_period u k) (embedding_integer_period v l) a

theorem elementaryProfile_exact_coefficient (τ : ℝ) (hτ : τ ≠ 0) (u z : d → ℝ) (a : Option (d × Bool)) :
    elementaryProfile τ u z a = τ * elementaryCoefficient (fun i => u i + τ * z i) u a := by
  cases a with
  | none => exact constantProfile_exact τ u z hτ
  | some a => exact coefficientProfile_exact τ u z hτ a

theorem elementaryProfile_fineLift (m : ℕ) (u v : d → ℝ) (a : Option (d × Bool)) :
    elementaryProfile (fineScale m) v (fineLift m u v) a = fineScale m * elementaryCoefficient u v a := by
  rw [elementaryProfile_exact_coefficient _ (fineScale_pos m).ne']
  simp only [fineLift_scaled]
  rw [elementaryCoefficient_embedding_eq _ v u v (centralDifference_embedding u v) rfl a]

theorem localizedProfile_original_exact (m : ℕ) (hm : 5 ≤ m) (u v : d → ℝ) (a : Option (d × Bool)) :
    localizedProfile annularCutoff a (fineScale m) v (fineLift m u v) =
      ((fineScale m * (fineCutoff m (truncatedDistance u v) * elementaryCoefficient u v a)) : ℝ) := by
  rw [localizedProfile_cutoff_exact a _ _ _ (fineLift_central m u v), elementaryProfile_fineLift,
    ← fineCutoff_profile_exact m hm]
  congr 1
  ring

theorem chordDistance_pos_of_truncated {u v : d → ℝ} (h : 0 < truncatedDistance u v) :
    0 < chordDistance u v := by
  have hn : chordDistance u v ≠ 0 := by
    intro hz
    have : truncatedDistance u v = 0 := by
      rw [truncatedDistance, hz, distanceCap_small (by norm_num)]
    linarith
  exact lt_of_le_of_ne (chordDistance_nonneg u v) (Ne.symm hn)

end CausalLowerbound.PartB.ShellGeometry

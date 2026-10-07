import CausalLowerbound.PartB.ElementaryCoefficients
import CausalLowerbound.MixedEvaluation

/-! The actual fine-shell elementary quotient, not merely an abstract local
profile, has a Wiener realization with the sharp single-factor scale 2^m. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB.ShellGeometry

open Wiener
variable {d : Type*} [Fintype d]

theorem fineLift_periodization (m : ℕ) (hm : 5 ≤ m) (u v : d → ℝ)
    (f : (d → ℝ) → ℂ) (hf : ∀ z, f z ≠ 0 → ∀ i, |z i| < 1) :
    periodize f (fun _ => 2 ^ m) (fun i => (2 : ℝ) ^ m * (u i - v i)) =
      f (fineLift m u v) := by
  have hp : (2 : ℝ) ≤ 2 ^ m := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ m by omega)
  have he : (fun i => (2 : ℝ) ^ m * (u i - v i)) =
      latticeTranslate (fun _ => 2 ^ m) (centralShift u v) (fineLift m u v) := by
    funext i
    simp only [latticeTranslate, fineLift, centralDifference, centralShift,
      Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [he, periodize_lattice_invariant]
  apply periodize_no_extra_copies_closed
  · intro z hz i
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (hf z hz i).trans_le (by linarith : 1 ≤ (2 : ℝ) ^ m / 2)
  · intro i
    simp only [fineLift, abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ m),
      Nat.cast_pow, Nat.cast_ofNat]
    nlinarith [centralDifference_abs u v i]

theorem localizedProfile_periodization_exact (m : ℕ) (hm : 5 ≤ m)
    (u v : d → ℝ) (a : Option (d × Bool)) :
    periodize (localizedProfile annularCutoff a (fineScale m) v) (fun _ => 2 ^ m)
      (fun i => (2 : ℝ) ^ m * (u i - v i)) =
      ((fineScale m * (fineCutoff m (truncatedDistance u v) * elementaryCoefficient u v a)) : ℝ) := by
  rw [fineLift_periodization m hm u v _ ?_, localizedProfile_original_exact m hm]
  intro z hz i
  have hκ : annularCutoff z ≠ 0 := by
    intro hzero
    exact hz (by simp only [localizedProfile, hzero, zero_mul, Complex.ofReal_zero])
  exact (annularCutoff_support_point z hκ).1 i

theorem localizedProfile_mixed_exact (m : ℕ) (hm : 5 ≤ m)
    (u v : d → ℝ) (a : Option (d × Bool)) :
    mixedPeriodizedTorus (fun y => localizedProfile annularCutoff a (fineScale m)
      (fun i => y (Sum.inl i)) (fun i => y (Sum.inr i))) (fun _ => 2 ^ m)
        (torusProjection (Sum.elim v (fun i => u i - v i))) =
      ((fineScale m * (fineCutoff m (truncatedDistance u v) * elementaryCoefficient u v a)) : ℝ) := by
  rw [mixedPeriodizedTorus_coe _ (fun k u z => localizedProfile_integer_period _ _ _ u z k)]
  simpa only [Sum.elim_inl, Sum.elim_inr, Nat.cast_pow, Nat.cast_ofNat] using
    localizedProfile_periodization_exact m hm u v a

/-- One constant works for every sufficiently fine dyadic level. Both the
periodization and the identification with the original quotient are proved. -/
theorem fine_edge_uniform_wiener (a : Option (d × Bool)) :
    ∃ m0 : ℕ, 5 ≤ m0 ∧ ∃ C ≥ 0, ∀ m, m0 ≤ m → ∃ A : Fourier (d ⊕ d),
      (∀ u v : d → ℝ, toContinuous A (torusProjection (Sum.elim v (fun i => u i - v i))) =
        ((fineCutoff m (truncatedDistance u v) * elementaryCoefficient u v a) : ℝ)) ∧
      ‖A‖ ≤ C * (2 : ℝ) ^ m := by
  obtain ⟨ε, hε, C, hC, hbound⟩ := explicit_fine_profile_wiener a
  obtain ⟨m0, hm0, hscale⟩ := exists_fine_start ε hε
  refine ⟨m0, hm0, C, hC, ?_⟩
  intro m hm
  obtain ⟨A, hA, hn⟩ := hbound (fineScale m) (hscale m hm) (fun _ => 2 ^ m)
    (fun _ => pow_ne_zero _ (by norm_num))
  refine ⟨((2 : ℝ) ^ m : ℂ) • A, ?_, ?_⟩
  · intro u v
    simp only [map_smul, ContinuousMap.smul_apply, smul_eq_mul]
    rw [hA, localizedProfile_mixed_exact m (hm0.trans hm)]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
    congr 1
    rw [← mul_assoc, fineScale, mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ m ≠ 0), one_mul]
  · rw [norm_smul, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ m)]
    exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (mul_comm _ _)

end CausalLowerbound.PartB.ShellGeometry

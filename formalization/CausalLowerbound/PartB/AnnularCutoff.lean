import CausalLowerbound.PartB.ChordBounds

/-! A fixed explicit annular cutoff equals one on every central fine shell.
Its support and smoothness are proved, so no cutoff existence is an input. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

variable {d : Type*} [Fintype d]

def annularCutoff (z : d → ℝ) : ℝ :=
  Real.smoothTransition ((64 * Real.pi ^ 2 * euclideanSquare z - 1) / 3) *
    ∏ i, Real.smoothTransition ((4 / 3 : ℝ) * (1 - (z i) ^ 2))

def annularSet : Set (d → ℝ) :=
  Set.Icc (fun _ => -1) (fun _ => 1) ∩ {z | 1 / (64 * Real.pi ^ 2) ≤ euclideanSquare z}

theorem annularSet_compact : IsCompact (annularSet (d := d)) :=
  isCompact_Icc.inter_right (isClosed_le continuous_const euclideanSquare_smooth.continuous)

theorem annularSet_avoids_zero : (0 : d → ℝ) ∉ annularSet := by
  intro h
  have := h.2
  simp only [euclideanSquare, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero, Set.mem_setOf_eq] at this
  have hp : 0 < (1 : ℝ) / (64 * Real.pi ^ 2) := by positivity
  linarith

theorem annularCutoff_smooth : ContDiff ℝ ∞ (annularCutoff (d := d)) := by
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul euclideanSquare_smooth).sub contDiff_const).div_const 3)
  · apply contDiff_prod
    intro i _
    exact Real.smoothTransition.contDiff.comp
      (contDiff_const.mul (contDiff_const.sub ((contDiff_apply ℝ ℝ i).pow 2)))

theorem annularCutoff_support_point (z : d → ℝ) (hz : annularCutoff z ≠ 0) :
    (∀ i, |z i| < 1) ∧ 1 / (64 * Real.pi ^ 2) < euclideanSquare z := by
  classical
  have hm := mul_ne_zero_iff.mp hz
  have hin : 0 < (64 * Real.pi ^ 2 * euclideanSquare z - 1) / 3 :=
    lt_of_not_ge (fun h => hm.1 (Real.smoothTransition.zero_of_nonpos h))
  refine ⟨?_, ?_⟩
  · intro i
    have hne := (Finset.prod_ne_zero_iff.mp hm.2) i (Finset.mem_univ i)
    have hout : 0 < (4 / 3 : ℝ) * (1 - (z i) ^ 2) :=
      lt_of_not_ge (fun h => hne (Real.smoothTransition.zero_of_nonpos h))
    nlinarith [sq_abs (z i), abs_nonneg (z i)]
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith

theorem annularCutoff_tsupport : tsupport (annularCutoff (d := d)) ⊆ annularSet := by
  apply closure_minimal _ annularSet_compact.isClosed
  intro z hz
  have h := annularCutoff_support_point z hz
  exact ⟨⟨fun i => (abs_lt.mp (h.1 i)).1.le, fun i => (abs_lt.mp (h.1 i)).2.le⟩, h.2.le⟩

theorem annularCutoff_compact : HasCompactSupport (annularCutoff (d := d)) :=
  annularSet_compact.of_isClosed_subset isClosed_closure annularCutoff_tsupport

theorem annularCutoff_avoids_zero : (0 : d → ℝ) ∉ tsupport annularCutoff :=
  fun h => annularSet_avoids_zero (annularCutoff_tsupport h)

theorem annularCutoff_eq_one (z : d → ℝ)
    (hs : 1 / (16 * Real.pi ^ 2) ≤ euclideanSquare z) (hz : ∀ i, |z i| ≤ 1 / 2) :
    annularCutoff z = 1 := by
  have hin : 1 ≤ (64 * Real.pi ^ 2 * euclideanSquare z - 1) / 3 := by
    have h := (div_le_iff₀ (by positivity : 0 < 16 * Real.pi ^ 2)).mp hs
    nlinarith
  rw [annularCutoff, Real.smoothTransition.one_of_one_le hin, one_mul]
  apply Finset.prod_eq_one
  intro i _
  apply Real.smoothTransition.one_of_one_le
  have hi := hz i
  nlinarith [sq_abs (z i), abs_nonneg (z i)]

theorem annularCutoff_on_fine_shell (τ : ℝ) (z : d → ℝ)
    (hz : ∀ i, |τ * z i| ≤ 1 / 2) (hρ : dyadicProfile (chordProfile τ z) ≠ 0) :
    annularCutoff z = 1 := by
  have h := fine_profile_annulus τ z hz hρ
  exact annularCutoff_eq_one z h.1.le (fun i => (h.2 i).le)

theorem localizedProfile_cutoff_exact (a : Option (d × Bool)) (τ : ℝ) (u z : d → ℝ)
    (hz : ∀ i, |τ * z i| ≤ 1 / 2) :
    localizedProfile annularCutoff a τ u z =
      (dyadicProfile (chordProfile τ z) * elementaryProfile τ u z a : ℝ) := by
  by_cases hρ : dyadicProfile (chordProfile τ z) = 0
  · simp only [localizedProfile, hρ, mul_zero, zero_mul]
  · rw [localizedProfile, annularCutoff_on_fine_shell τ z hz hρ, one_mul]

/-- The former arbitrary annular cutoff is now fully supplied by an explicit
formula which has been proved not to change the central shell multiplier. -/
theorem explicit_fine_profile_wiener (a : Option (d × Bool)) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ τ ∈ Set.Icc 0 ε, ∀ N : d → ℕ, (∀ i, N i ≠ 0) →
      ∃ A : Wiener.Fourier (d ⊕ d),
        (∀ x, Wiener.toContinuous A x = Wiener.mixedPeriodizedTorus
          (fun y => localizedProfile annularCutoff a τ
            (fun i => y (Sum.inl i)) (fun i => y (Sum.inr i))) N x) ∧ ‖A‖ ≤ C :=
  localizedProfile_uniform_wiener annularCutoff annularCutoff_smooth
    annularCutoff_compact annularCutoff_avoids_zero a

end CausalLowerbound.PartB.ShellGeometry

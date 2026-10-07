import CausalLowerbound.MixedPeriodization

/-! Evaluate mixed periodizations on chosen real representatives. Closed
central lifts are allowed, because the profile support is strictly central. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.Wiener

variable {U Z : Type*} [Fintype U] [Fintype Z]

theorem edgePeriodize_integer_invariant (H : (U ⊕ Z → ℝ) → ℂ)
    (hper : ∀ k u z, H (Sum.elim (latticeTranslate (fun _ => 1) k u) z) = H (Sum.elim u z))
    (N : Z → ℕ) (k : U → ℤ) (l : Z → ℤ) (u : U → ℝ) (z : Z → ℝ) :
    edgePeriodize H N (Sum.elim (latticeTranslate (fun _ => 1) k u) (latticeTranslate N l z)) =
      edgePeriodize H N (Sum.elim u z) := by
  have he : edgePeriodize H N
      (Sum.elim (latticeTranslate (fun _ => 1) k u) (latticeTranslate N l z)) =
      periodize (fun y => H (Sum.elim u y)) N (latticeTranslate N l z) := by
    unfold edgePeriodize periodize
    apply tsum_congr
    intro j
    exact hper k u (latticeTranslate N j (latticeTranslate N l z))
  rw [he, periodize_lattice_invariant]
  rfl

theorem mixedPeriodizedTorus_coe (H : (U ⊕ Z → ℝ) → ℂ)
    (hper : ∀ k u z, H (Sum.elim (latticeTranslate (fun _ => 1) k u) z) = H (Sum.elim u z))
    (N : Z → ℕ) (x : U ⊕ Z → ℝ) :
    mixedPeriodizedTorus H N (torusProjection x) =
      periodize (fun z => H (Sum.elim (fun i => x (Sum.inl i)) z)) N
        (fun i => (N i : ℝ) * x (Sum.inr i)) := by
  obtain ⟨k, hk⟩ := torusProjection_eq_integer_shift (torusRepresentative (torusProjection x)) x
    (torusProjection_representative _)
  have he : coordinateScale (mixedPeriods N) (torusRepresentative (torusProjection x)) =
      Sum.elim (latticeTranslate (fun _ => 1) (fun i => k (Sum.inl i)) (fun i => x (Sum.inl i)))
        (latticeTranslate N (fun i => k (Sum.inr i)) (fun i => (N i : ℝ) * x (Sum.inr i))) := by
    funext i
    rw [hk]
    cases i with
    | inl i => simp [coordinateScale, mixedPeriods, latticeTranslate]
    | inr i => simp only [coordinateScale, mixedPeriods, Sum.elim_inr, latticeTranslate]; ring
  unfold mixedPeriodizedTorus
  rw [he, edgePeriodize_integer_invariant H hper]
  rfl

theorem periodize_no_extra_copies_closed (f : (Z → ℝ) → ℂ) (N : Z → ℕ)
    (hsupport : ∀ y, f y ≠ 0 → ∀ i, |y i| < (N i : ℝ) / 2)
    (x : Z → ℝ) (hx : ∀ i, |x i| ≤ (N i : ℝ) / 2) : periodize f N x = f x := by
  classical
  have hz : ∀ k : Z → ℤ, k ≠ 0 → f (latticeTranslate N k x) = 0 := by
    intro k hk
    have he : ∃ i, k i ≠ 0 := by
      by_contra! h
      exact hk (funext h)
    obtain ⟨i, hi⟩ := he
    by_contra hn
    have hki : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
    have hy := hsupport _ hn i
    have hle : (N i : ℝ) ≤ |(latticeTranslate N k x) i - x i| := by
      simpa [latticeTranslate, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ N i from Nat.cast_nonneg _)] using
        mul_le_mul_of_nonneg_left hki (Nat.cast_nonneg (N i))
    have htri := abs_sub ((latticeTranslate N k x) i) (x i)
    linarith [hx i]
  calc
    periodize f N x = f (latticeTranslate N 0 x) := tsum_eq_single 0 hz
    _ = f x := by congr 1; funext i; simp [latticeTranslate]

end CausalLowerbound.Wiener

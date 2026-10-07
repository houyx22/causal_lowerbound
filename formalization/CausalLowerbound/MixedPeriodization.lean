import CausalLowerbound.SmoothWindow
import CausalLowerbound.CompactPeriodizedFamily

/-! Mixed periodic-base / compact-edge profiles. A fixed smooth window in
the base coordinates gives an exact compact representation, so the genuine
Wiener estimate applies to the partially periodized profile itself. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators

namespace CausalLowerbound.Wiener

variable {U Z : Type*} [Fintype U] [Fintype Z]

def mixedPeriods (N : Z → ℕ) : U ⊕ Z → ℕ := Sum.elim (fun _ => 1) N

def compactify (H : (U ⊕ Z → ℝ) → ℂ) (x : U ⊕ Z → ℝ) : ℂ :=
  windowProduct (fun i => x (Sum.inl i)) * H x

def edgePeriodize (H : (U ⊕ Z → ℝ) → ℂ) (N : Z → ℕ) (x : U ⊕ Z → ℝ) : ℂ :=
  ∑' k : Z → ℤ, H (Sum.elim (fun i => x (Sum.inl i))
    (latticeTranslate N k (fun i => x (Sum.inr i))))

def mixedPeriodizedTorus (H : (U ⊕ Z → ℝ) → ℂ) (N : Z → ℕ) (x : Torus (U ⊕ Z)) : ℂ :=
  edgePeriodize H N (coordinateScale (mixedPeriods N) (torusRepresentative x))

theorem mixedPeriods_ne_zero (N : Z → ℕ) (hN : ∀ i, N i ≠ 0) :
    ∀ i : U ⊕ Z, mixedPeriods N i ≠ 0 := by
  intro i
  cases i with
  | inl i => exact one_ne_zero
  | inr i => exact hN i

theorem periodize_summable (f : (U → ℝ) → ℂ) (hf : HasCompactSupport f)
    (N : U → ℕ) (hN : ∀ i, N i ≠ 0) (x : U → ℝ) :
    Summable (fun k => f (latticeTranslate N k x)) := by
  obtain ⟨S, hS⟩ := periodize_finite_on_compact f hf N hN {x} isCompact_singleton
  exact summable_of_ne_finset_zero (hS x (Set.mem_singleton x))

theorem periodize_compactify (H : (U ⊕ Z → ℝ) → ℂ) (hH : HasCompactSupport (compactify H))
    (hper : ∀ k u z, H (Sum.elim (latticeTranslate (fun _ => 1) k u) z) = H (Sum.elim u z))
    (N : Z → ℕ) (hN : ∀ i, N i ≠ 0) (x : U ⊕ Z → ℝ) :
    periodize (compactify H) (mixedPeriods N) x = edgePeriodize H N x := by
  let e := Equiv.sumArrowEquivProdArrow U Z ℤ
  let u := fun i => x (Sum.inl i)
  let z := fun i => x (Sum.inr i)
  let F := fun p : (U → ℤ) × (Z → ℤ) =>
    windowProduct (latticeTranslate (fun _ => 1) p.1 u) * H (Sum.elim u (latticeTranslate N p.2 z))
  have he (p : (U → ℤ) × (Z → ℤ)) :
      compactify H (latticeTranslate (mixedPeriods N) (e.symm p) x) = F p := by
    have he' : latticeTranslate (mixedPeriods N) (e.symm p) x =
        Sum.elim (latticeTranslate (fun _ => 1) p.1 u) (latticeTranslate N p.2 z) := by
      funext i
      cases i <;> rfl
    rw [he']
    change windowProduct (latticeTranslate (fun _ => 1) p.1 u) *
      H (Sum.elim (latticeTranslate (fun _ => 1) p.1 u) (latticeTranslate N p.2 z)) = F p
    rw [hper]
  have hs0 := periodize_summable (compactify H) hH (mixedPeriods N) (mixedPeriods_ne_zero N hN) x
  have hs : Summable F := (hs0.comp_injective e.symm.injective).congr he
  have hinner (k : U → ℤ) : Summable (fun l : Z → ℤ => F (k, l)) :=
    hs.comp_injective (fun _ _ h => congrArg Prod.snd h)
  unfold periodize
  rw [← e.symm.tsum_eq]
  simp only [he]
  rw [hs.tsum_prod' hinner]
  simp only [F, tsum_mul_left, tsum_mul_right]
  change periodize windowProduct (fun _ => 1) u * edgePeriodize H N x = edgePeriodize H N x
  rw [periodize_windowProduct, one_mul]

theorem periodizedTorus_compactify (H : (U ⊕ Z → ℝ) → ℂ)
    (hH : HasCompactSupport (compactify H))
    (hper : ∀ k u z, H (Sum.elim (latticeTranslate (fun _ => 1) k u) z) = H (Sum.elim u z))
    (N : Z → ℕ) (hN : ∀ i, N i ≠ 0) (x : Torus (U ⊕ Z)) :
    periodizedTorus (compactify H) (mixedPeriods N) x = mixedPeriodizedTorus H N x :=
  periodize_compactify H hH hper N hN _

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem compactify_family_support (H : P × (U ⊕ Z → ℝ) → ℂ)
    (Kp : Set P) (Kz : Set (Z → ℝ)) (hKz : IsCompact Kz)
    (hsupport : ∀ p ∈ Kp, ∀ x, H (p, x) ≠ 0 → (fun i => x (Sum.inr i)) ∈ Kz) :
    ∃ K : Set (U ⊕ Z → ℝ), IsCompact K ∧
      ∀ p ∈ Kp, tsupport (compactify (fun x => H (p, x))) ⊆ K := by
  let e : (U ⊕ Z → ℝ) ≃ₜ (U → ℝ) × (Z → ℝ) := Homeomorph.sumArrowHomeomorphProdArrow
  let K := e.symm '' (Set.Icc (fun _ => -1) (fun _ => 1) ×ˢ Kz)
  have hK : IsCompact K := (isCompact_Icc.prod hKz).image e.symm.continuous
  refine ⟨K, hK, ?_⟩
  intro p hp
  apply closure_minimal _ hK.isClosed
  intro x hx
  have hmul := mul_ne_zero_iff.mp hx
  refine ⟨e x, ⟨windowProduct_support (subset_tsupport _ hmul.1),
    hsupport p hp x hmul.2⟩, e.symm_apply_apply x⟩

theorem compactify_family_smooth (H : P × (U ⊕ Z → ℝ) → ℂ) (p : P) (x : U ⊕ Z → ℝ)
    (hf : ContDiffAt ℝ ∞ H (p, x)) :
    ContDiffAt ℝ ∞ (fun y : P × (U ⊕ Z → ℝ) => compactify (fun z => H (y.1, z)) y.2) (p, x) := by
  have hw : ContDiff ℝ ∞ (fun y : P × (U ⊕ Z → ℝ) =>
      windowProduct (fun i => y.2 (Sum.inl i))) :=
    windowProduct_smooth.comp (contDiff_pi.mpr (fun i =>
      (contDiff_apply ℝ ℝ (Sum.inl i)).comp contDiff_snd))
  exact hw.contDiffAt.mul hf

/-- The paper's mixed profile estimate, using joint smoothness and one
compact set in the Euclidean edge coordinates. -/
theorem mixed_family_wiener (H : P × (U ⊕ Z → ℝ) → ℂ)
    (Kp : Set P) (Kz : Set (Z → ℝ)) (hKp : IsCompact Kp) (hKz : IsCompact Kz)
    (hsupport : ∀ p ∈ Kp, ∀ x, H (p, x) ≠ 0 → (fun i => x (Sum.inr i)) ∈ Kz)
    (hf : ∀ p ∈ Kp, ∀ x, ContDiffAt ℝ ∞ H (p, x))
    (hper : ∀ p ∈ Kp, ∀ k u z,
      H (p, Sum.elim (latticeTranslate (fun _ => 1) k u) z) = H (p, Sum.elim u z)) :
    ∃ C ≥ 0, ∀ p ∈ Kp, ∀ N : Z → ℕ, (∀ i, N i ≠ 0) →
      ∃ A : Fourier (U ⊕ Z), (∀ x, toContinuous A x = mixedPeriodizedTorus (fun y => H (p, y)) N x) ∧
        ‖A‖ ≤ C := by
  obtain ⟨K, hK, hs⟩ := compactify_family_support H Kp Kz hKz hsupport
  obtain ⟨C, hC, hb⟩ := compact_family_periodized_wiener
    (fun y : P × (U ⊕ Z → ℝ) => compactify (fun z => H (y.1, z)) y.2) Kp K hKp hK hs
    (fun p hp x _ => compactify_family_smooth H p x (hf p hp x))
  refine ⟨C, hC, ?_⟩
  intro p hp N hN
  obtain ⟨A, hA, hnorm⟩ := hb p hp (mixedPeriods N) (mixedPeriods_ne_zero N hN)
  refine ⟨A, ?_, hnorm⟩
  intro x
  rw [hA, periodizedTorus_compactify _ (hK.of_isClosed_subset isClosed_closure (hs p hp))
    (hper p hp) N hN]

variable {V E d : Type*} [Fintype V] [DecidableEq V] [Fintype E] [Fintype d]

theorem mixed_family_configuration_wiener (a b : E → V)
    (H : P × (((V × d) ⊕ (E × d)) → ℝ) → ℂ)
    (Kp : Set P) (Kz : Set ((E × d) → ℝ)) (hKp : IsCompact Kp) (hKz : IsCompact Kz)
    (hsupport : ∀ p ∈ Kp, ∀ x, H (p, x) ≠ 0 → (fun i => x (Sum.inr i)) ∈ Kz)
    (hf : ∀ p ∈ Kp, ∀ x, ContDiffAt ℝ ∞ H (p, x))
    (hper : ∀ p ∈ Kp, ∀ k u z,
      H (p, Sum.elim (latticeTranslate (fun _ => 1) k u) z) = H (p, Sum.elim u z)) :
    ∃ C ≥ 0, ∀ p ∈ Kp, ∀ N : (E × d) → ℕ, (∀ i, N i ≠ 0) →
      ∃ A : Fourier (V × d), (∀ x, toContinuous A x =
        mixedPeriodizedTorus (fun y => H (p, y)) N (configurationLift a b x)) ∧ ‖A‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := mixed_family_wiener H Kp Kz hKp hKz hsupport hf hper
  refine ⟨C, hC, ?_⟩
  intro p hp N hN
  obtain ⟨A, hA, hnorm⟩ := hb p hp N hN
  refine ⟨configurationPullback a b A, ?_, (configurationPullback_bound a b A).trans hnorm⟩
  intro x
  rw [configurationPullback_value, hA]

end CausalLowerbound.Wiener

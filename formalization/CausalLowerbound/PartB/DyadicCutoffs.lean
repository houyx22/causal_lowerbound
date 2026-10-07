import CausalLowerbound.PartB.TaperShellBudget
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Explicit nonnegative smooth dyadic cutoffs and the coarse remainder.
The partition telescopes exactly and is finite at every positive radius. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators

namespace CausalLowerbound.PartB

theorem expNegInvGlue_monotone : Monotone expNegInvGlue := by
  intro x y hxy
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx]
    exact expNegInvGlue.nonneg y
  · have hx0 : 0 < x := lt_of_not_ge hx
    have hy0 : 0 < y := hx0.trans_le hxy
    simp only [expNegInvGlue, if_neg hx, if_neg hy0.not_le]
    exact Real.exp_le_exp.mpr (neg_le_neg (inv_anti₀ hx0 hxy))

theorem smoothTransition_monotone : Monotone Real.smoothTransition := by
  intro x y hxy
  unfold Real.smoothTransition
  rw [div_le_div_iff₀ (Real.smoothTransition.pos_denom x) (Real.smoothTransition.pos_denom y)]
  have h := mul_le_mul (expNegInvGlue_monotone hxy)
    (expNegInvGlue_monotone (sub_le_sub_left hxy 1))
    (expNegInvGlue.nonneg (1 - y)) (expNegInvGlue.nonneg y)
  nlinarith

def dyadicProfile (r : ℝ) : ℝ := Real.smoothTransition (2 * r - 1) - Real.smoothTransition (r - 1)

theorem dyadicProfile_smooth : ContDiff ℝ ∞ dyadicProfile :=
  (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).sub
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem dyadicProfile_zero_left {r : ℝ} (hr : r ≤ 1 / 2) : dyadicProfile r = 0 := by
  rw [dyadicProfile, Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_self]

theorem dyadicProfile_zero_right {r : ℝ} (hr : 2 ≤ r) : dyadicProfile r = 0 := by
  rw [dyadicProfile, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), sub_self]

theorem dyadicProfile_nonneg (r : ℝ) : 0 ≤ dyadicProfile r := by
  by_cases hr : 0 ≤ r
  · exact sub_nonneg.mpr (smoothTransition_monotone (by linarith))
  · rw [dyadicProfile_zero_left (by linarith)]

theorem dyadicProfile_support {r : ℝ} (hr : dyadicProfile r ≠ 0) : 1 / 2 < r ∧ r < 2 :=
  ⟨lt_of_not_ge (fun h => hr (dyadicProfile_zero_left h)),
    lt_of_not_ge (fun h => hr (dyadicProfile_zero_right h))⟩

theorem dyadicProfile_tsupport : tsupport dyadicProfile ⊆ Set.Icc (1 / 2) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro r hr
  exact ⟨(dyadicProfile_support hr).1.le, (dyadicProfile_support hr).2.le⟩

theorem dyadicProfile_compact : HasCompactSupport dyadicProfile :=
  isCompact_Icc.of_isClosed_subset isClosed_closure dyadicProfile_tsupport

def fineCutoff (m : ℕ) (r : ℝ) : ℝ := dyadicProfile ((2 : ℝ) ^ m * r)

def coarseCutoff (m0 : ℕ) (r : ℝ) : ℝ := Real.smoothTransition ((2 : ℝ) ^ m0 * r - 1)

theorem fineCutoff_smooth (m : ℕ) : ContDiff ℝ ∞ (fineCutoff m) :=
  dyadicProfile_smooth.comp (contDiff_const.mul contDiff_id)

theorem coarseCutoff_smooth (m0 : ℕ) : ContDiff ℝ ∞ (coarseCutoff m0) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem fineCutoff_nonneg (m : ℕ) (r : ℝ) : 0 ≤ fineCutoff m r := dyadicProfile_nonneg _

theorem coarseCutoff_nonneg (m0 : ℕ) (r : ℝ) : 0 ≤ coarseCutoff m0 r :=
  Real.smoothTransition.nonneg _

theorem fineCutoff_support (m : ℕ) (r : ℝ) (hr : fineCutoff m r ≠ 0) :
    1 / (2 : ℝ) ^ (m + 1) < r ∧ r < 2 / (2 : ℝ) ^ m := by
  have h := dyadicProfile_support hr
  constructor
  · rw [div_lt_iff₀ (by positivity)]
    rw [pow_succ]
    nlinarith [h.1]
  · exact (lt_div_iff₀ (by positivity)).mpr (by nlinarith [h.2])

theorem coarseCutoff_zero (m0 : ℕ) {r : ℝ} (hr : r ≤ 1 / (2 : ℝ) ^ m0) :
    coarseCutoff m0 r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h := (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ m0)).mp hr
  nlinarith

theorem dyadic_partial_partition (m0 L : ℕ) (r : ℝ) :
    coarseCutoff m0 r + ∑ j ∈ Finset.range L, fineCutoff (m0 + j) r = coarseCutoff (m0 + L) r := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    unfold fineCutoff dyadicProfile coarseCutoff
    rw [show m0 + (L + 1) = (m0 + L) + 1 by omega, pow_succ]
    congr 1 <;> ring

/-- At every positive radius the partition is already a finite sum; all
finer shells vanish. The coarse shell is the actual telescoping remainder. -/
theorem dyadic_finite_partition (m0 : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ L : ℕ, (coarseCutoff m0 r + ∑ j ∈ Finset.range L, fineCutoff (m0 + j) r = 1) ∧
      ∀ j, L ≤ j → fineCutoff (m0 + j) r = 0 := by
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (2 / r) (by norm_num : (1 : ℝ) < 2)
  have hpow (j : ℕ) (hj : L ≤ j) : 2 < (2 : ℝ) ^ (m0 + j) * r := by
    have hle : (2 : ℝ) ^ L ≤ 2 ^ (m0 + j) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact (div_lt_iff₀ hr).mp (hL.trans_le hle)
  refine ⟨L, ?_, ?_⟩
  · rw [dyadic_partial_partition]
    exact Real.smoothTransition.one_of_one_le (by linarith [hpow L le_rfl])
  · intro j hj
    exact dyadicProfile_zero_right (hpow j hj).le

def shellLevel (m0 : ℕ) : Option ℕ → ℕ := fun s => s.elim 0 (fun m => m0 + m)

def shellCutoff (m0 : ℕ) : Option ℕ → ℝ → ℝ :=
  fun s => s.elim (coarseCutoff m0) (fun m => fineCutoff (m0 + m))

theorem shellCutoff_upper (m0 : ℕ) (s : Option ℕ) (r : ℝ) (hr : r ≤ 1)
    (hs : shellCutoff m0 s r ≠ 0) : r ≤ 2 / (2 : ℝ) ^ shellLevel m0 s := by
  cases s with
  | none => simpa [shellLevel] using hr.trans (by norm_num : (1 : ℝ) ≤ 2)
  | some m => exact (fineCutoff_support (m0 + m) r hs).2.le

def taperCutoff (r : ℝ) : ℝ := Real.smoothTransition (r - 1)

theorem taperCutoff_smooth : ContDiff ℝ ∞ taperCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem taperCutoff_zero {r : ℝ} (hr : r ≤ 1) : taperCutoff r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem taperCutoff_one {r : ℝ} (hr : 2 ≤ r) : taperCutoff r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem shellLevel_injective (m0 : ℕ) (hm0 : 0 < m0) : Function.Injective (shellLevel m0) := by
  intro s t h
  cases s with
  | none =>
    cases t with
    | none => rfl
    | some j => change 0 = m0 + j at h; omega
  | some i =>
    cases t with
    | none => change m0 + i = 0 at h; omega
    | some j =>
      congr 1
      change m0 + i = m0 + j at h
      omega

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

open ConfigurationShells

/-- Admissibility follows from the actual cutoffs and taper at every
configuration whose edge distances lie in `[0,1]`. -/
theorem concrete_shell_admissible (m0 : ℕ) (a b : E → V) (s : E → Option ℕ)
    (t : ℝ) (ht : 0 < t) (r : E → ℝ) (hr : ∀ e, r e ∈ Set.Icc 0 1)
    (h : graphTaper a b taperCutoff t r * shellWeight (fun e => shellCutoff m0 (s e)) r ≠ 0) :
    Admissible a b (levelBudget ((2 : ℝ) ^ Fintype.card E) t) (fun e => shellLevel m0 (s e)) := by
  intro i
  have htaper := taper_nonzero_vertexProduct a b taperCutoff (fun _ _ hx => taperCutoff_zero hx)
    t ht r (fun e => (hr e).1) (mul_ne_zero_iff.mp h).1 i
  have hρ := (mul_ne_zero_iff.mp h).2
  have hs := vertexProduct_shell_bound a b r (fun e => (hr e).1)
    (fun e => shellLevel m0 (s e)) 2 (by norm_num)
    (fun e => shellCutoff_upper m0 (s e) (r e) (hr e).2
      ((Finset.prod_ne_zero_iff.mp hρ) e (Finset.mem_univ e))) i
  apply level_le_budget
  apply le_of_lt
  apply (lt_div_iff₀ ht).mpr
  have hh := (lt_div_iff₀ (by positivity)).mp (htaper.trans_le hs)
  simpa only [mul_comm] using hh

/-- The coarse label and the fine labels are counted without identifying
them. Positivity of the starting fine level makes the level code injective. -/
theorem concrete_shell_card_bound (m0 : ℕ) (hm0 : 0 < m0) (a b : E → V) (L : ℕ) :
    Nat.card {s : E → Option ℕ // Admissible a b L (fun e => shellLevel m0 (s e))} ≤
      (L + 1) ^ Fintype.card E := by
  classical
  let S := {s : E → Option ℕ // Admissible a b L (fun e => shellLevel m0 (s e))}
  let code : S → E → Fin (L + 1) := fun s e =>
    ⟨shellLevel m0 (s.val e), Nat.lt_succ_of_le
      ((edge_le_vertexOrder a b (fun e => shellLevel m0 (s.val e)) e).trans (s.property (a e)))⟩
  have hinj : Function.Injective code := by
    intro s t h
    apply Subtype.ext
    funext e
    apply shellLevel_injective m0 hm0
    exact congrArg Fin.val (congrFun h e)
  letI : Finite S := Finite.of_injective code hinj
  letI : Fintype S := Fintype.ofFinite S
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective code hinj

end CausalLowerbound.PartB

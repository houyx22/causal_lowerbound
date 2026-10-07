import CausalLowerbound.PeriodizedWiener
import CausalLowerbound.WienerSpatialShift

/-! A compact one-dimensional profile can be put at any interior point of
the unit chart and narrowed by any positive integer factor. Its actual
Wiener norm is bounded independently of both choices. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace CausalLowerbound.Wiener

def intervalProfile (f : ℝ → ℂ) (x : Fin 1 → ℝ) : ℂ := f (x 0)

theorem intervalProfile_compact (f : ℝ → ℂ) (hf : HasCompactSupport f) :
    HasCompactSupport (intervalProfile f) :=
  hf.comp_homeomorph (Homeomorph.funUnique (Fin 1) ℝ)

theorem intervalProfile_smooth (f : ℝ → ℂ) (hs : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (intervalProfile f) := hs.comp (contDiff_apply ℝ ℝ 0)

def intervalWiener (f : ℝ → ℂ) (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f)
    (N : ℕ) (hN : N ≠ 0) (a : ℝ) : Fourier (Fin 1) :=
  spatialShift (torusProjection (fun _ => -a))
    (periodizedWiener (intervalProfile f) (intervalProfile_compact f hf)
      ((intervalProfile_smooth f hs).of_le (WithTop.coe_le_coe.mpr le_top)) (fun _ => N) (fun _ => hN))

def intervalWienerConstant (f : ℝ → ℂ) : ℝ :=
  derivativeDecayConstant (fun y : EuclideanSpace ℝ (Fin 1) => intervalProfile f (fun i => y i)) 1 *
    latticeConstant

theorem intervalWiener_bound (f : ℝ → ℂ) (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f)
    (N : ℕ) (hN : N ≠ 0) (a : ℝ) :
    ‖intervalWiener f hf hs N hN a‖ ≤ intervalWienerConstant f := by
  rw [intervalWiener, spatialShift_norm]
  simpa only [intervalWienerConstant, Fintype.card_fin, pow_one] using
    periodizedWiener_bound (intervalProfile f) (intervalProfile_compact f hf)
      ((intervalProfile_smooth f hs).of_le (WithTop.coe_le_coe.mpr le_top)) (fun _ => N) (fun _ => hN)

theorem intervalWienerConstant_nonneg (f : ℝ → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) : 0 ≤ intervalWienerConstant f :=
  (norm_nonneg _).trans (intervalWiener_bound f hf hs 1 (by decide) 0)

theorem intervalProfile_no_extra_copies (f : ℝ → ℂ)
    (hsupport : ∀ y, f y ≠ 0 → |y| < 1) (N : ℕ) (hN : 4 ≤ N)
    (a : ℝ) (ha : a ∈ Set.Icc (1 / 4) (3 / 4))
    (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    periodize (intervalProfile f) (fun _ => N) (fun _ => (N : ℝ) * (x - a)) =
      f ((N : ℝ) * (x - a)) := by
  classical
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hz (k : Fin 1 → ℤ) (hk : k ≠ 0) :
      intervalProfile f (latticeTranslate (fun _ => N) k (fun _ => (N : ℝ) * (x - a))) = 0 := by
    have hk0 : k 0 ≠ 0 := by
      intro h
      apply hk
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using h
    by_contra h
    have hh := hsupport _ h
    change |(N : ℝ) * (x - a) + (N : ℝ) * (k 0 : ℝ)| < 1 at hh
    rw [← mul_add] at hh
    by_cases hp : 0 ≤ k 0
    · have hk1 : (1 : ℝ) ≤ k 0 := by exact_mod_cast (show (1 : ℤ) ≤ k 0 by omega)
      have hb : 1 ≤ (N : ℝ) * (x - a + k 0) := calc
        1 ≤ (N : ℝ) * (1 / 4) := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hx.1, ha.2]) (by positivity)
      exact (not_lt_of_ge (hb.trans (le_abs_self _))) hh
    · have hk1 : (k 0 : ℝ) ≤ -1 := by exact_mod_cast (show k 0 ≤ (-1 : ℤ) by omega)
      have hb : (N : ℝ) * (x - a + k 0) ≤ -1 := calc
        _ ≤ (N : ℝ) * (-1 / 4) :=
          mul_le_mul_of_nonneg_left (by linarith [hx.2, ha.1]) (by positivity)
        _ ≤ -1 := by linarith
      have hh' := neg_le_abs ((N : ℝ) * (x - a + k 0))
      linarith
  rw [periodize, tsum_eq_single 0 hz]
  simp [intervalProfile, latticeTranslate]

theorem intervalWiener_value (f : ℝ → ℂ) (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f)
    (hsupport : ∀ y, f y ≠ 0 → |y| < 1) (N : ℕ) (hN : 4 ≤ N)
    (a : ℝ) (ha : a ∈ Set.Icc (1 / 4) (3 / 4)) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    toContinuous (intervalWiener f hf hs N (by omega) a) (torusProjection (fun _ => x)) =
      f ((N : ℝ) * (x - a)) := by
  rw [intervalWiener, spatialShift_value, periodizedWiener_value]
  have he : torusProjection (fun _ : Fin 1 => x) + torusProjection (fun _ => -a) =
      torusProjection (fun _ => x - a) := by
    funext i
    simp only [torusProjection, Pi.add_apply, sub_eq_add_neg, QuotientAddGroup.mk_add]
  rw [he, periodizedTorus_coe]
  exact intervalProfile_no_extra_copies f hsupport N hN a ha x hx

end CausalLowerbound.Wiener

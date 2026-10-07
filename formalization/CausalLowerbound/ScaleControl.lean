import CausalLowerbound.HolderScaling

/-! A calculus for actual derivatives with a common spatial scale. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace CausalLowerbound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure ScaleControl (M : ℕ) (r C : ℝ) (f : E → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  scale_pos : 0 < r
  nonneg : 0 ≤ C
  bound : ∀ j ≤ M, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C * r⁻¹ ^ j

namespace ScaleControl
variable {M : ℕ} {r C D : ℝ} {f g : E → ℝ}

theorem mono (h : ScaleControl M r C f) (hCD : C ≤ D) : ScaleControl M r D f :=
  ⟨h.smooth, h.scale_pos, h.nonneg.trans hCD, fun j hj x => (h.bound j hj x).trans
    (mul_le_mul_of_nonneg_right hCD (pow_nonneg (inv_nonneg.mpr h.scale_pos.le) _))⟩

theorem const (M : ℕ) (r c : ℝ) (hr : 0 < r) : ScaleControl M r |c| (fun _ : E => c) := by
  refine ⟨contDiff_const, hr, abs_nonneg _, ?_⟩
  intro j hj x
  by_cases hj0 : j = 0
  · subst j; simp [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_const_of_ne hj0, Pi.zero_apply, norm_zero]
    positivity

theorem add (hf : ScaleControl M r C f) (hg : ScaleControl M r D g) :
    ScaleControl M r (C + D) (fun x => f x + g x) := by
  refine ⟨hf.smooth.add hg.smooth, hf.scale_pos, add_nonneg hf.nonneg hg.nonneg, ?_⟩
  intro j hj x
  rw [iteratedFDeriv_add_apply'
    ((hf.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
    ((hg.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt), add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hf.bound j hj x) (hg.bound j hj x))

theorem smul (hf : ScaleControl M r C f) (a : ℝ) :
    ScaleControl M r (|a| * C) (fun x => a * f x) := by
  refine ⟨contDiff_const.mul hf.smooth, hf.scale_pos, mul_nonneg (abs_nonneg _) hf.nonneg, ?_⟩
  intro j hj x
  have he : iteratedFDeriv ℝ j (fun y => a * f y) x = a • iteratedFDeriv ℝ j f x :=
    by
      simpa only [smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply' (a := a) (f := f) (i := j) (x := x)
          ((hf.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt))
  rw [he]
  calc
    _ ≤ |a| * ‖iteratedFDeriv ℝ j f x‖ := by simpa using norm_smul_le a (iteratedFDeriv ℝ j f x)
    _ ≤ |a| * (C * r⁻¹ ^ j) := mul_le_mul_of_nonneg_left (hf.bound j hj x) (abs_nonneg _)
    _ = _ := by ring

theorem smul_le (hf : ScaleControl M r C f) (a A : ℝ) (ha : |a| ≤ A) :
    ScaleControl M r (A * C) (fun x => a * f x) :=
  (hf.smul a).mono (mul_le_mul_of_nonneg_right ha hf.nonneg)

theorem neg (hf : ScaleControl M r C f) : ScaleControl M r C (fun x => -f x) := by
  simpa using hf.smul (-1)

theorem sub (hf : ScaleControl M r C f) (hg : ScaleControl M r D g) :
    ScaleControl M r (C + D) (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : ScaleControl M r C f) (hg : ScaleControl M r D g) (hr : 0 < r) :
    ScaleControl M r ((2 : ℝ) ^ M * C * D) (fun x => f x * g x) :=
  ⟨hf.smooth.mul hg.smooth, hr, mul_nonneg (mul_nonneg (by positivity) hf.nonneg) hg.nonneg,
    derivative_scale_product f g hf.smooth hg.smooth M C D r hf.nonneg hg.nonneg hr hf.bound hg.bound⟩

theorem finer (hf : ScaleControl M r C f) {s : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    ScaleControl M s C f := by
  refine ⟨hf.smooth, hs, hf.nonneg, ?_⟩
  intro j hj x
  exact (hf.bound j hj x).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (inv_nonneg.mpr (hs.trans_le hsr).le) (inv_anti₀ hs hsr) j) hf.nonneg)

theorem holder {m : ℕ} {θ : ℝ} (hf : ScaleControl (m + 1) r C f)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) :
    HolderControl m θ (2 * C * r ^ (-((m : ℝ) + θ))) f := by
  simpa only [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le] using
    derivative_scale_holder f hf.smooth m θ C r hθ hθ1 hf.nonneg hr hr1 hf.bound

theorem amplitude_holder {m : ℕ} {θ : ℝ} (hf : ScaleControl (m + 1) r C f)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (c : ℝ) (hc : 0 ≤ c) :
    HolderControl m θ (2 * C * c) (fun x => (c * r ^ ((m : ℝ) + θ)) * f x) := by
  have hh := (hf.holder hθ hθ1 hr hr1).const_smul hf.smooth (c * r ^ ((m : ℝ) + θ))
  have he : |c * r ^ ((m : ℝ) + θ)| * (2 * C * r ^ (-((m : ℝ) + θ))) = 2 * C * c := by
    rw [abs_of_nonneg (mul_nonneg hc (Real.rpow_nonneg hr.le _)), Real.rpow_neg hr.le]
    have hp := (Real.rpow_pos_of_pos hr ((m : ℝ) + θ)).ne'
    field_simp
    ring
  simpa only [he, smul_eq_mul] using hh
end ScaleControl

theorem HolderControl.const (m : ℕ) (θ c : ℝ) : HolderControl m θ |c| (fun _ : E => c) := by
  constructor
  · intro j hj x
    by_cases hj0 : j = 0
    · subst j; simp [norm_iteratedFDeriv_zero]
    · simp [iteratedFDeriv_const_of_ne hj0, abs_nonneg]
  · intro x y
    have he : iteratedFDeriv ℝ m (fun _ : E => c) x = iteratedFDeriv ℝ m (fun _ : E => c) y := by
      by_cases hm : m = 0
      · subst m; simp [iteratedFDeriv_zero_eq_comp]
      · simp [iteratedFDeriv_const_of_ne hm]
    rw [he, sub_self, norm_zero]
    positivity

theorem HolderControl.half_shift {m : ℕ} {θ C : ℝ} {f : E → ℝ}
    (hf : HolderControl m θ C f) (hs : ContDiff ℝ ∞ f) :
    HolderControl m θ (1 / 2 + C / 2) (fun x => (1 + f x) / 2) := by
  have hh := (HolderControl.const (E := E) m θ (1 / 2)).add (hf.const_smul hs (1 / 2))
    contDiff_const (contDiff_const.smul hs)
  have he : |(1 / 2 : ℝ)| + |(1 / 2 : ℝ)| * C = 1 / 2 + C / 2 := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    ring
  rw [he] at hh
  convert hh using 1
  funext x
  simp only [smul_eq_mul]
  ring
end CausalLowerbound

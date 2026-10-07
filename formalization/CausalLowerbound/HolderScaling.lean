import CausalLowerbound.SmoothCompact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Global isotropic Hölder bounds, including noninteger orders, with the
exact small-scale exponent. Constants are uniform in the translation and
scale. The bounded-overlap packet assembly is a separate application. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators NNReal

namespace CausalLowerbound

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Global derivative and fractional seminorm control of order m+θ.
For θ=0 the last condition is just bounded oscillation of the m-th derivative. -/
def HolderControl (m : ℕ) (θ C : ℝ) (f : E → F) : Prop :=
  (∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C) ∧
    ∀ x y, ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ ≤ C * ‖x - y‖ ^ θ

theorem HolderControl.value_bound {m : ℕ} {θ C : ℝ} {f : E → F}
    (h : HolderControl m θ C f) (x : E) : ‖f x‖ ≤ C := by
  simpa only [norm_iteratedFDeriv_zero] using h.1 0 (Nat.zero_le m) x

theorem HolderControl.mono {m : ℕ} {θ C D : ℝ} {f : E → F}
    (h : HolderControl m θ C f) (hCD : C ≤ D) : HolderControl m θ D f := by
  exact ⟨fun j hj x => (h.1 j hj x).trans hCD,
    fun x y => (h.2 x y).trans (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg (norm_nonneg _) _))⟩

theorem HolderControl.const_smul {m : ℕ} {θ C : ℝ} {f : E → F}
    (h : HolderControl m θ C f) (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    HolderControl m θ (|a| * C) (fun x => a • f x) := by
  have he (j : ℕ) (x : E) : iteratedFDeriv ℝ j (fun y => a • f y) x =
      a • iteratedFDeriv ℝ j f x :=
    iteratedFDeriv_const_smul_apply' ((hf.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
  constructor
  · intro j hj x
    rw [he]
    calc
      _ ≤ ‖a‖ * ‖iteratedFDeriv ℝ j f x‖ := norm_smul_le a _
      _ ≤ _ := by simpa only [Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_left (h.1 j hj x) (norm_nonneg a)
  · intro x y
    rw [he, he, ← smul_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.2 x y) (abs_nonneg a)

theorem HolderControl.add {m : ℕ} {θ C D : ℝ} {f g : E → F}
    (ha : HolderControl m θ C f) (hb : HolderControl m θ D g)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    HolderControl m θ (C + D) (fun x => f x + g x) := by
  have he (j : ℕ) (x : E) : iteratedFDeriv ℝ j (fun y => f y + g y) x =
      iteratedFDeriv ℝ j f x + iteratedFDeriv ℝ j g x :=
    iteratedFDeriv_add_apply' ((hf.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
      ((hg.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
  constructor
  · intro j hj x
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (ha.1 j hj x) (hb.1 j hj x))
  · intro x y
    rw [he, he]
    have hh : iteratedFDeriv ℝ m f x + iteratedFDeriv ℝ m g x -
        (iteratedFDeriv ℝ m f y + iteratedFDeriv ℝ m g y) =
        (iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y) +
          (iteratedFDeriv ℝ m g x - iteratedFDeriv ℝ m g y) := by abel
    rw [hh, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (ha.2 x y) (hb.2 x y))

def rescaled (f : E → F) (c : E) (r : ℝ) (x : E) : F := f (r⁻¹ • (x - c))

theorem rescaled_smooth (f : E → F) (hf : ContDiff ℝ ∞ f) (c : E) (r : ℝ) :
    ContDiff ℝ ∞ (rescaled f c r) :=
  hf.comp (contDiff_const.smul (contDiff_id.sub contDiff_const))

theorem rescaled_derivative_bound (f : E → F) (hf : ContDiff ℝ ∞ f)
    (c : E) (r : ℝ) (hr : 0 < r) (j : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) (x : E) :
    ‖iteratedFDeriv ℝ j (rescaled f c r) x‖ ≤ B * (r⁻¹) ^ j := by
  let L : E →L[ℝ] E := r⁻¹ • ContinuousLinearMap.id ℝ E
  have hL : ‖L‖ ≤ r⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hr.le)
    intro y
    simp [L, norm_smul, abs_of_pos hr]
  have he : iteratedFDeriv ℝ j (rescaled f c r) x =
      (iteratedFDeriv ℝ j f (L (x - c))).compContinuousLinearMap (fun _ => L) := by
    change iteratedFDeriv ℝ j (fun y => (f ∘ L) (y - c)) x = _
    rw [iteratedFDeriv_comp_sub]
    exact L.iteratedFDeriv_comp_right hf (x - c)
      (WithTop.coe_le_coe.mpr le_top)
  rw [he]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : (∏ _i : Fin j, ‖L‖) ≤ r⁻¹ ^ j := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod (s := (Finset.univ : Finset (Fin j)))
        (fun _ _ => norm_nonneg L) (fun _ _ => hL)
  exact mul_le_mul (hb _) hp (Finset.prod_nonneg (fun _ _ => norm_nonneg L)) hB

theorem compact_smooth_derivatives_bounded (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (M : ℕ) :
    ∃ B > 0, ∀ j ≤ M, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
  have hb (j : ℕ) : ∃ B, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B :=
    (hc.iteratedFDeriv j).exists_bound_of_continuous
      (ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top) hf)
  choose b hb using hb
  refine ⟨1 + ∑ j ∈ Finset.range (M + 1), |b j|, by positivity, ?_⟩
  intro j hj x
  have hmem : j ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
  have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (M + 1)) => abs_nonneg (b j)) hmem
  exact (hb j x).trans ((le_abs_self _).trans (hs.trans (by linarith)))

/-- Boundedness controls large distances; the derivative controls small ones.
Their combination gives every fractional exponent in [0,1]. -/
theorem fractional_bound_from_two_bounds (f : E → F) (A r θ : ℝ)
    (hA : 0 ≤ A) (hr : 0 < r) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hb : ∀ x, ‖f x‖ ≤ A)
    (hl : ∀ x y, ‖f x - f y‖ ≤ A * (‖x - y‖ / r)) (x y : E) :
    ‖f x - f y‖ ≤ 2 * A * (‖x - y‖ / r) ^ θ := by
  let z := ‖x - y‖ / r
  have hz : 0 ≤ z := div_nonneg (norm_nonneg _) hr.le
  have hp : 0 ≤ z ^ θ := Real.rpow_nonneg hz _
  by_cases hz1 : z ≤ 1
  · have hh := mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_le_one hz hz1 hθ1) hA
    have hfxy := hl x y
    change ‖f x - f y‖ ≤ 2 * A * z ^ θ
    nlinarith
  · have hp1 := Real.one_le_rpow (le_of_not_ge hz1) hθ
    have hfxy := (norm_sub_le (f x) (f y)).trans (add_le_add (hb x) (hb y))
    change ‖f x - f y‖ ≤ 2 * A * z ^ θ
    nlinarith

theorem derivative_scale_holder (f : E → F) (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (θ B r : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hB : 0 ≤ B)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hb : ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B * r⁻¹ ^ j) :
    HolderControl m θ (2 * B * r⁻¹ ^ ((m : ℝ) + θ)) f := by
  have hrinv : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr hr1
  have hA : 0 ≤ B * r⁻¹ ^ m := mul_nonneg hB (pow_nonneg (inv_nonneg.mpr hr.le) _)
  constructor
  · intro j hj x
    have hh : (r⁻¹ : ℝ) ^ j ≤ r⁻¹ ^ ((m : ℝ) + θ) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hrinv
      have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
      linarith
    have hp := Real.rpow_nonneg (inv_nonneg.mpr hr.le) ((m : ℝ) + θ)
    exact (hb j (by omega) x).trans ((mul_le_mul_of_nonneg_left hh hB).trans (by nlinarith))
  · have hd : Differentiable ℝ (iteratedFDeriv ℝ m f) :=
      ContDiff.differentiable_iteratedFDeriv (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top m)) hf
    let C : ℝ≥0 := ⟨B * r⁻¹ ^ (m + 1), mul_nonneg hB (pow_nonneg (inv_nonneg.mpr hr.le) _)⟩
    have hlip : LipschitzWith C (iteratedFDeriv ℝ m f) :=
      lipschitzWith_of_nnnorm_fderiv_le hd (fun x => by
        change ‖fderiv ℝ (iteratedFDeriv ℝ m f) x‖ ≤ B * r⁻¹ ^ (m + 1)
        rw [norm_fderiv_iteratedFDeriv]
        exact hb (m + 1) le_rfl x)
    intro x y
    have hfrac := fractional_bound_from_two_bounds (iteratedFDeriv ℝ m f)
      (B * r⁻¹ ^ m) r θ hA hr hθ hθ1 (hb m (by omega))
      (fun x y => by
        have h := hlip.norm_sub_le x y
        change ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ ≤
          (B * r⁻¹ ^ (m + 1)) * ‖x - y‖ at h
        simpa only [pow_succ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h) x y
    apply hfrac.trans_eq
    rw [Real.div_rpow (norm_nonneg _) hr.le,
      Real.rpow_add (inv_pos.mpr hr), Real.rpow_natCast, Real.inv_rpow hr.le]
    ring

/-- `lem:holder-scaling` for a single smooth compactly supported profile,
with all translations, all 0<r≤1, and every fractional exponent θ∈[0,1]. -/
theorem compact_smooth_holder_scaling (f : E → F) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C > 0, ∀ c r, 0 < r → r ≤ 1 →
      HolderControl m θ (C * r ^ (-((m : ℝ) + θ))) (rescaled f c r) := by
  obtain ⟨B, hB, hb⟩ := compact_smooth_derivatives_bounded f hf hc (m + 1)
  refine ⟨2 * B, by positivity, ?_⟩
  intro c r hr hr1
  have h := derivative_scale_holder (rescaled f c r) (rescaled_smooth f hf c r)
    m θ B r hθ hθ1 hB.le hr hr1 (fun j hj x =>
      rescaled_derivative_bound f hf c r hr j B hB.le (hb j hj) x)
  simpa only [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le] using h

theorem derivative_scale_product (f g : E → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (M : ℕ) (A B r : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 < r)
    (ha : ∀ j ≤ M, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A * r⁻¹ ^ j)
    (hb : ∀ j ≤ M, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ B * r⁻¹ ^ j) :
    ∀ j ≤ M, ∀ x, ‖iteratedFDeriv ℝ j (fun y => f y * g y) x‖ ≤
      ((2 : ℝ) ^ M * A * B) * r⁻¹ ^ j := by
  intro j hj x
  refine (norm_iteratedFDeriv_mul_le hf hg x (WithTop.coe_le_coe.mpr le_top)).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (A * r⁻¹ ^ i) * (B * r⁻¹ ^ (j - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (ha i (hi'.trans hj) x) (Nat.cast_nonneg _))
        (hb (j - i) ((Nat.sub_le _ _).trans hj) x) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hA (pow_nonneg (inv_nonneg.mpr hr.le) _)))
    _ = (2 : ℝ) ^ j * A * B * r⁻¹ ^ j := by
      have he (i : ℕ) (hi : i ∈ Finset.range (j + 1)) :
          (j.choose i : ℝ) * (A * r⁻¹ ^ i) * (B * r⁻¹ ^ (j - i)) =
            (j.choose i : ℝ) * (A * B * r⁻¹ ^ j) := by
        have hi' : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
        have hp : r⁻¹ ^ i * r⁻¹ ^ (j - i) = r⁻¹ ^ j := by rw [← pow_add, Nat.add_sub_of_le hi']
        calc
          _ = (j.choose i : ℝ) * (A * B * (r⁻¹ ^ i * r⁻¹ ^ (j - i))) := by ring
          _ = _ := by rw [hp]
      rw [Finset.sum_congr rfl he, ← Finset.sum_mul]
      have hc : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [hc]
      ring
    _ ≤ _ := by
      have hh := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hj
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hA) hB)
        (pow_nonneg (inv_nonneg.mpr hr.le) _)

/-- Only the number of supports meeting a point enters this bound, not the
total number of summands. -/
theorem derivative_scale_bounded_overlap {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → E → F) (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i))
    (M N : ℕ) (B r : ℝ) (hB : 0 ≤ B) (hr : 0 < r)
    (hb : ∀ i ∈ S, ∀ j ≤ M, ∀ x, ‖iteratedFDeriv ℝ j (f i) x‖ ≤ B * r⁻¹ ^ j)
    (hoverlap : ∀ x, ∃ T : Finset ι, T ⊆ S ∧ T.card ≤ N ∧
      ∀ i ∈ S, x ∈ tsupport (f i) → i ∈ T) :
    ∀ j ≤ M, ∀ x, ‖iteratedFDeriv ℝ j (fun y => ∑ i ∈ S, f i y) x‖ ≤
      ((N : ℝ) * B) * r⁻¹ ^ j := by
  intro j hj x
  obtain ⟨T, hTS, hTN, hT⟩ := hoverlap x
  rw [iteratedFDeriv_sum (fun i hi => (hf i hi).of_le (WithTop.coe_le_coe.mpr le_top))]
  simp only [Finset.sum_apply]
  change ‖∑ i ∈ S, iteratedFDeriv ℝ j (f i) x‖ ≤ _
  have hz : ∀ i ∈ S, i ∉ T → iteratedFDeriv ℝ j (f i) x = 0 := by
    intro i hi hni
    by_contra hn
    exact hni (hT i hi (support_iteratedFDeriv_subset j hn))
  rw [← Finset.sum_subset hTS hz]
  calc
    _ ≤ ∑ i ∈ T, ‖iteratedFDeriv ℝ j (f i) x‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ T, B * r⁻¹ ^ j := Finset.sum_le_sum (fun i hi => hb i (hTS hi) j hj x)
    _ = (T.card : ℝ) * (B * r⁻¹ ^ j) := by simp
    _ ≤ _ := by
      have hh : (T.card : ℝ) ≤ N := by exact_mod_cast hTN
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh
        (mul_nonneg hB (pow_nonneg (inv_nonneg.mpr hr.le) _))

end CausalLowerbound

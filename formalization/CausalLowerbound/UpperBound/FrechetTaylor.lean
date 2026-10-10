import CausalLowerbound.UpperBound.HolderTaylor
import CausalLowerbound.HolderScaling

/-! The multivariate Taylor remainder for the project's existing isotropic
Hölder control.  The polynomial is expressed intrinsically through Fréchet
derivatives, so the result works in every real normed space. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators

namespace CausalLowerbound.UpperBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def frechetTaylor (f : E → ℝ) (q : ℕ) (x y : E) : ℝ :=
  ∑ k ∈ Finset.range (q + 1),
    (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k f x (fun _ => y - x)

theorem iteratedDeriv_ray (f : E → ℝ) (x v : E) (k : ℕ)
    (hf : ContDiff ℝ k f) (t : ℝ) :
    iteratedDeriv k (fun s : ℝ => f (x + s • v)) t =
      iteratedFDeriv ℝ k f (x + t • v) (fun _ => v) := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hg : ContDiffAt ℝ k (fun y => f (x + y)) (L t) :=
    hf.contDiffAt.comp _ (contDiffAt_const.add contDiffAt_id)
  have he := iteratedFDeriv_comp_linear_at (fun y => f (x + y)) L t k hg
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ k ((fun y => f (x + y)) ∘ L) t) (fun _ => 1) = _
  rw [he]
  simp [iteratedFDeriv_comp_add_left, L]

theorem iteratedDerivWithin_eq_of_contDiff {f : ℝ → ℝ} {q : ℕ}
    (hf : ContDiff ℝ q f) {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin q f s x = iteratedDeriv q f x := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedFDerivWithin_eq_iteratedFDeriv hs hf.contDiffAt hx,
    iteratedDeriv_eq_iteratedFDeriv]

theorem taylor_ray_eq_frechetTaylor {f : E → ℝ} {q : ℕ}
    (hf : ContDiff ℝ q f) (x y : E) :
    taylorWithinEval (fun t : ℝ => f (x + t • (y - x))) q (Icc 0 1) 0 1 =
      frechetTaylor f q x y := by
  rw [taylor_within_apply]
  unfold frechetTaylor
  apply Finset.sum_congr rfl
  intro k hk
  have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hfk : ContDiff ℝ k f := hf.of_le (by exact_mod_cast hkq)
  have hφ : ContDiff ℝ k (fun t : ℝ => f (x + t • (y - x))) :=
    hfk.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  rw [iteratedDerivWithin_eq_of_contDiff hφ (uniqueDiffOn_Icc (by norm_num))
      (by norm_num), iteratedDeriv_ray f x (y - x) k hfk]
  simp

theorem ray_highest_derivative_holder {f : E → ℝ} {q : ℕ} {C θ : ℝ}
    (hf : ContDiff ℝ q f) (hholder : HolderControl q θ C f) (hθ : 0 ≤ θ)
    (x v : E) (t : ℝ) :
    |iteratedDeriv q (fun s : ℝ => f (x + s • v)) t -
      iteratedDeriv q (fun s : ℝ => f (x + s • v)) 0| ≤
      (C * ‖v‖ ^ ((q : ℝ) + θ)) * |t| ^ θ := by
  rw [iteratedDeriv_ray f x v q hf, iteratedDeriv_ray f x v q hf]
  simp only [zero_smul, add_zero]
  have hm : |iteratedFDeriv ℝ q f (x + t • v) (fun _ => v) -
      iteratedFDeriv ℝ q f x (fun _ => v)| ≤
      ‖iteratedFDeriv ℝ q f (x + t • v) - iteratedFDeriv ℝ q f x‖ * ‖v‖ ^ q := by
    simpa only [ContinuousMultilinearMap.sub_apply, Real.norm_eq_abs,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (iteratedFDeriv ℝ q f (x + t • v) - iteratedFDeriv ℝ q f x).le_opNorm (fun _ => v)
  calc
    _ ≤ (C * ‖(x + t • v) - x‖ ^ θ) * ‖v‖ ^ q :=
      hm.trans (mul_le_mul_of_nonneg_right (hholder.2 _ _) (pow_nonneg (norm_nonneg _) _))
    _ = _ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        Real.mul_rpow (abs_nonneg t) (norm_nonneg v),
        Real.rpow_add_of_nonneg (norm_nonneg v) (Nat.cast_nonneg q) hθ,
        Real.rpow_natCast]
      ring

/-- Quantitative multivariate Hölder--Taylor remainder, with no extra
derivative beyond those in `HolderControl` and `ContDiff`. -/
theorem holder_frechetTaylor_remainder {f : E → ℝ} {q : ℕ} {C θ : ℝ}
    (hf : ContDiff ℝ q f) (hholder : HolderControl q θ C f)
    (hC : 0 ≤ C) (hθ : 0 ≤ θ) (x y : E) :
    |f y - frechetTaylor f q x y| ≤ C * ‖y - x‖ ^ ((q : ℝ) + θ) / q.factorial := by
  let φ : ℝ → ℝ := fun t => f (x + t • (y - x))
  have hφ : ContDiff ℝ q φ :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hh (t : ℝ) :
      |iteratedDeriv q φ t - iteratedDeriv q φ 0| ≤
        (C * ‖y - x‖ ^ ((q : ℝ) + θ)) * |t| ^ θ :=
    ray_highest_derivative_holder hf hholder hθ x (y - x) t
  rw [← taylor_ray_eq_frechetTaylor hf x y]
  change |f y - taylorWithinEval φ q (Icc 0 1) 0 1| ≤ _
  cases q with
  | zero =>
      have he := hh 1
      simpa [φ] using he
  | succ n =>
      have hwithin (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
          iteratedDerivWithin (n + 1) φ (Icc 0 1) t = iteratedDeriv (n + 1) φ t :=
        iteratedDerivWithin_eq_of_contDiff hφ (uniqueDiffOn_Icc (by norm_num)) ht
      have he := holder_taylor_remainder_succ (by norm_num : (0 : ℝ) < 1)
        (by positivity : 0 ≤ C * ‖y - x‖ ^ ((n + 1 : ℕ) + θ)) hθ hφ.contDiffOn
        (fun t ht => by
          rw [hwithin t ht, hwithin 0 (by norm_num)]
          simpa only [sub_zero] using hh t)
      simpa [φ] using he

end CausalLowerbound.UpperBound

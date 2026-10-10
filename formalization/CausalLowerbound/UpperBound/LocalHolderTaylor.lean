import CausalLowerbound.UpperBound.FrechetTaylor

/-! Local Hölder extensions suffice.  The Taylor segment lies in an open
neighborhood of the cube; no regularity outside that neighborhood is used. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators

namespace CausalLowerbound.UpperBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HolderControlOn (q : ℕ) (θ C : ℝ) (f : E → ℝ) (U : Set E) : Prop :=
  (∀ k ≤ q, ∀ x ∈ U, ‖iteratedFDeriv ℝ k f x‖ ≤ C) ∧
    ∀ x ∈ U, ∀ y ∈ U,
      ‖iteratedFDeriv ℝ q f x - iteratedFDeriv ℝ q f y‖ ≤ C * ‖x - y‖ ^ θ

theorem HolderControlOn.of_global {q : ℕ} {θ C : ℝ} {f : E → ℝ}
    (hf : HolderControl q θ C f) (U : Set E) : HolderControlOn q θ C f U :=
  ⟨fun k hk x _ => hf.1 k hk x, fun x _ y _ => hf.2 x y⟩

theorem iteratedDeriv_ray_of_contDiffAt (f : E → ℝ) (x v : E) (k : ℕ) (t : ℝ)
    (hf : ContDiffAt ℝ k f (x + t • v)) :
    iteratedDeriv k (fun s : ℝ => f (x + s • v)) t =
      iteratedFDeriv ℝ k f (x + t • v) (fun _ => v) := by
  let L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hg : ContDiffAt ℝ k (fun y => f (x + y)) (L t) :=
    hf.comp _ (contDiffAt_const.add contDiffAt_id)
  have he := iteratedFDeriv_comp_linear_at (fun y => f (x + y)) L t k hg
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ k ((fun y => f (x + y)) ∘ L) t) (fun _ => 1) = _
  rw [he]
  simp [iteratedFDeriv_comp_add_left, L]

theorem iteratedDerivWithin_eq_of_contDiffAt {f : ℝ → ℝ} {q : ℕ} {x : ℝ}
    (hf : ContDiffAt ℝ q f x) {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) :
    iteratedDerivWithin q f s x = iteratedDeriv q f x := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedFDerivWithin_eq_iteratedFDeriv hs hf hx,
    iteratedDeriv_eq_iteratedFDeriv]

theorem taylor_ray_eq_frechetTaylor_of_contDiffAt {f : E → ℝ} {q : ℕ} (x y : E)
    (hf : ContDiffAt ℝ q f x) :
    taylorWithinEval (fun t : ℝ => f (x + t • (y - x))) q (Icc 0 1) 0 1 =
      frechetTaylor f q x y := by
  rw [taylor_within_apply]
  unfold frechetTaylor
  apply Finset.sum_congr rfl
  intro k hk
  have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hfk : ContDiffAt ℝ k f x := hf.of_le (by exact_mod_cast hkq)
  have hfx : ContDiffAt ℝ k f (x + (0 : ℝ) • (y - x)) := by simpa using hfk
  have hφ : ContDiffAt ℝ k (fun t : ℝ => f (x + t • (y - x))) 0 :=
    hfx.comp 0 (show ContDiffAt ℝ k (fun t : ℝ => x + t • (y - x)) 0 from
      (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt)
  rw [iteratedDerivWithin_eq_of_contDiffAt hφ (uniqueDiffOn_Icc (by norm_num))
      (by norm_num), iteratedDeriv_ray_of_contDiffAt f x (y - x) k 0 hfx]
  simp

theorem local_ray_highest_derivative_holder {f : E → ℝ} {q : ℕ} {C θ : ℝ}
    {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ q f U)
    (hholder : HolderControlOn q θ C f U) (hθ : 0 ≤ θ)
    (x v : E) (t : ℝ) (hx : x ∈ U) (ht : x + t • v ∈ U) :
    |iteratedDeriv q (fun s : ℝ => f (x + s • v)) t -
      iteratedDeriv q (fun s : ℝ => f (x + s • v)) 0| ≤
      (C * ‖v‖ ^ ((q : ℝ) + θ)) * |t| ^ θ := by
  have hx' : x + (0 : ℝ) • v ∈ U := by simpa using hx
  rw [iteratedDeriv_ray_of_contDiffAt f x v q t (hf.contDiffAt (hU.mem_nhds ht)),
    iteratedDeriv_ray_of_contDiffAt f x v q 0 (hf.contDiffAt (hU.mem_nhds hx'))]
  simp only [zero_smul, add_zero]
  have hm : |iteratedFDeriv ℝ q f (x + t • v) (fun _ => v) -
      iteratedFDeriv ℝ q f x (fun _ => v)| ≤
      ‖iteratedFDeriv ℝ q f (x + t • v) - iteratedFDeriv ℝ q f x‖ * ‖v‖ ^ q := by
    simpa only [ContinuousMultilinearMap.sub_apply, Real.norm_eq_abs,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (iteratedFDeriv ℝ q f (x + t • v) - iteratedFDeriv ℝ q f x).le_opNorm (fun _ => v)
  calc
    _ ≤ (C * ‖(x + t • v) - x‖ ^ θ) * ‖v‖ ^ q :=
      hm.trans (mul_le_mul_of_nonneg_right (hholder.2 _ ht _ hx)
        (pow_nonneg (norm_nonneg _) _))
    _ = _ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        Real.mul_rpow (abs_nonneg t) (norm_nonneg v),
        Real.rpow_add_of_nonneg (norm_nonneg v) (Nat.cast_nonneg q) hθ,
        Real.rpow_natCast]
      ring

theorem holder_frechetTaylor_remainder_on {f : E → ℝ} {q : ℕ} {C θ : ℝ}
    {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ q f U)
    (hholder : HolderControlOn q θ C f U) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (x y : E) (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ U) :
    |f y - frechetTaylor f q x y| ≤ C * ‖y - x‖ ^ ((q : ℝ) + θ) / q.factorial := by
  let φ : ℝ → ℝ := fun t => f (x + t • (y - x))
  have hx : x ∈ U := by simpa using hsegment 0 (by norm_num)
  have hφ : ContDiffOn ℝ q φ (Icc 0 1) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn hsegment
  have hφat (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ q φ t :=
    (hf.contDiffAt (hU.mem_nhds (hsegment t ht))).comp t
      (show ContDiffAt ℝ q (fun s : ℝ => x + s • (y - x)) t from
        (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt)
  have hh (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |iteratedDeriv q φ t - iteratedDeriv q φ 0| ≤
        (C * ‖y - x‖ ^ ((q : ℝ) + θ)) * |t| ^ θ :=
    local_ray_highest_derivative_holder hU hf hholder hθ x (y - x) t hx (hsegment t ht)
  rw [← taylor_ray_eq_frechetTaylor_of_contDiffAt x y (hf.contDiffAt (hU.mem_nhds hx))]
  change |f y - taylorWithinEval φ q (Icc 0 1) 0 1| ≤ _
  cases q with
  | zero =>
      have he := hh 1 (by norm_num)
      simpa [φ] using he
  | succ n =>
      have hwithin (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
          iteratedDerivWithin (n + 1) φ (Icc 0 1) t = iteratedDeriv (n + 1) φ t :=
        iteratedDerivWithin_eq_of_contDiffAt (hφat t ht) (uniqueDiffOn_Icc (by norm_num)) ht
      have he := holder_taylor_remainder_succ (by norm_num : (0 : ℝ) < 1)
        (by positivity : 0 ≤ C * ‖y - x‖ ^ ((n + 1 : ℕ) + θ)) hθ hφ
        (fun t ht => by
          rw [hwithin t ht, hwithin 0 (by norm_num)]
          simpa only [sub_zero] using hh t ht)
      simpa [φ] using he

end CausalLowerbound.UpperBound
